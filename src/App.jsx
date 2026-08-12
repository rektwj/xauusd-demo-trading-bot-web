import React, { useState, useEffect, useRef, useCallback, useMemo } from "react";

/* =========================================================================
   XAUUSD DEMO TRADING TERMINAL
   - Harga real dari XAUS.com API (no key, CORS open) -> TIDAK PERNAH di-hardcode/fake.
   - Eksekusi order = PAPER TRADING lokal (tersimpan di storage pribadi browser).
     Bot ini TIDAK terhubung ke broker MT4/MT5 manapun -- lihat panel "Broker
     Bridge" untuk penjelasan kenapa, dan interface abstraction untuk nanti.
   ========================================================================= */

const SPOT_URL = "https://xaus.com/api/v1/spot?currency=IDR&compact=1";
const INTRADAY_URL = "https://xaus.com/api/v1/intraday?symbol=xau&hours=48";
const HISTORY_URL = "https://xaus.com/api/v1/history";

const TIMEFRAMES = [
  { key: "1m", minutes: 1, label: "1m" },
  { key: "5m", minutes: 5, label: "5m" },
  { key: "15m", minutes: 15, label: "15m" },
  { key: "30m", minutes: 30, label: "30m" },
  { key: "1H", minutes: 60, label: "1H" },
  { key: "4H", minutes: 240, label: "4H" },
  { key: "1D", minutes: 1440, label: "1D" },
];

const LOT_OZ = 100; // 1 standard lot XAUUSD = 100 troy oz (konvensi umum broker)
const DEFAULT_BALANCE_IDR = 100_000_000;
const RISK_PER_TRADE = 0.005; // 0.5%
const MAX_OPEN_POSITIONS = 3;
const MAX_DAILY_LOSS_PCT = 0.02; // 2%
const MAX_CONSECUTIVE_LOSSES = 3;
const MIN_CONFIDENCE_TO_TRADE = 85;
const STALE_AFTER_SEC = 90; // > ini => DELAYED
const OFFLINE_AFTER_SEC = 300; // > ini, atau fetch gagal => OFFLINE

/* ---------------------------- helpers: format ---------------------------- */
const fmtIDR = (n) =>
  "Rp" + Math.round(n || 0).toLocaleString("id-ID", { maximumFractionDigits: 0 });
const fmtUSD = (n) => "$" + (n ?? 0).toFixed(2);
const fmtPct = (n) => (n ?? 0).toFixed(1) + "%";
const nowIso = () => new Date().toISOString();

/* ---------------------------- indicator math ------------------------------ */
function ema(values, period) {
  if (values.length === 0) return [];
  const k = 2 / (period + 1);
  const out = [values[0]];
  for (let i = 1; i < values.length; i++) out.push(values[i] * k + out[i - 1] * (1 - k));
  return out;
}
function rsi(values, period = 14) {
  const out = new Array(values.length).fill(null);
  if (values.length < period + 1) return out;
  let gains = 0, losses = 0;
  for (let i = 1; i <= period; i++) {
    const d = values[i] - values[i - 1];
    if (d >= 0) gains += d; else losses -= d;
  }
  let avgGain = gains / period, avgLoss = losses / period;
  out[period] = avgLoss === 0 ? 100 : 100 - 100 / (1 + avgGain / avgLoss);
  for (let i = period + 1; i < values.length; i++) {
    const d = values[i] - values[i - 1];
    const gain = d > 0 ? d : 0, loss = d < 0 ? -d : 0;
    avgGain = (avgGain * (period - 1) + gain) / period;
    avgLoss = (avgLoss * (period - 1) + loss) / period;
    out[i] = avgLoss === 0 ? 100 : 100 - 100 / (1 + avgGain / avgLoss);
  }
  return out;
}
function macd(values) {
  const e12 = ema(values, 12), e26 = ema(values, 26);
  const line = values.map((_, i) => e12[i] - e26[i]);
  const signal = ema(line, 9);
  const hist = line.map((v, i) => v - signal[i]);
  return { line, signal, hist };
}
function atr(candles, period = 14) {
  const trs = candles.map((c, i) => {
    if (i === 0) return c.high - c.low;
    const prevClose = candles[i - 1].close;
    return Math.max(c.high - c.low, Math.abs(c.high - prevClose), Math.abs(c.low - prevClose));
  });
  return ema(trs, period);
}
function findSwings(candles, lookback = 3) {
  const highs = [], lows = [];
  for (let i = lookback; i < candles.length - lookback; i++) {
    const windowC = candles.slice(i - lookback, i + lookback + 1);
    const h = candles[i].high, l = candles[i].low;
    if (h === Math.max(...windowC.map((c) => c.high))) highs.push({ i, price: h });
    if (l === Math.min(...windowC.map((c) => c.low))) lows.push({ i, price: l });
  }
  return { highs, lows };
}

/* ---------------------------- candle aggregation --------------------------- */
// rawPoints: [{t: ms, p: price}] ascending -> OHLC candles per intervalMinutes
function aggregateCandles(rawPoints, intervalMinutes) {
  if (!rawPoints.length) return [];
  const bucketMs = intervalMinutes * 60 * 1000;
  const buckets = new Map();
  for (const { t, p } of rawPoints) {
    const b = Math.floor(t / bucketMs) * bucketMs;
    if (!buckets.has(b)) buckets.set(b, { time: b, open: p, high: p, low: p, close: p });
    const c = buckets.get(b);
    c.high = Math.max(c.high, p);
    c.low = Math.min(c.low, p);
    c.close = p;
  }
  return Array.from(buckets.values()).sort((a, b) => a.time - b.time);
}

/* =============================== APP =============================== */
export default function App() {
  const [spot, setSpot] = useState(null); // last /spot response
  const [connState, setConnState] = useState("OFFLINE"); // LIVE / DELAYED / OFFLINE
  const [fetchError, setFetchError] = useState(null);
  const [rawPoints, setRawPoints] = useState([]); // combined intraday + live-polled points
  const [historyDaily, setHistoryDaily] = useState([]);
  const [timeframe, setTimeframe] = useState("15m");
  const [account, setAccount] = useState(null);
  const [autoTrading, setAutoTrading] = useState(false);
  const [botStopped, setBotStopped] = useState(false);
  const [storageReady, setStorageReady] = useState(false);
  const pollRef = useRef(null);
  const liveSamplesRef = useRef([]); // local high-res samples this session

  /* -------- Broker Bridge (MT4/MT5 via MetaApi bridge server Anda) -------- */
  const [bridgeConfig, setBridgeConfig] = useState({ url: "", key: "" });
  const [bridgeStatus, setBridgeStatus] = useState({ checking: false, connected: false, isDemo: false, allowReal: false, error: null });
  const [bridgeAccount, setBridgeAccount] = useState(null);
  const [bridgePositions, setBridgePositions] = useState([]);
  // Terhubung & boleh eksekusi kalau: akun demo, ATAU akun real yang sudah di-opt-in eksplisit
  // lewat ALLOW_REAL_TRADING=true di server bridge (server tetap membatasi volume order-nya).
  const bridgeConnected = bridgeStatus.connected && (bridgeStatus.isDemo || bridgeStatus.allowReal);
  const bridgeIsRealMoney = bridgeConnected && !bridgeStatus.isDemo;

  useEffect(() => {
    try {
      const raw = localStorage.getItem("bridge-config");
      if (raw) setBridgeConfig(JSON.parse(raw));
    } catch { /* belum ada config tersimpan */ }
  }, []);

  const saveBridgeConfig = useCallback(async (cfg) => {
    setBridgeConfig(cfg);
    try { localStorage.setItem("bridge-config", JSON.stringify(cfg)); } catch {}
  }, []);

  const bridgeFetch = useCallback(async (path, opts = {}) => {
    if (!bridgeConfig.url) throw new Error("Bridge URL belum diisi");
    const res = await fetch(bridgeConfig.url.replace(/\/$/, "") + path, {
      ...opts,
      headers: { "Content-Type": "application/json", "x-bridge-key": bridgeConfig.key, ...(opts.headers || {}) },
    });
    const data = await res.json();
    if (!res.ok) throw new Error(data.error || data.message || `HTTP ${res.status}`);
    return data;
  }, [bridgeConfig]);

  const checkBridge = useCallback(async () => {
    if (!bridgeConfig.url) return;
    setBridgeStatus((s) => ({ ...s, checking: true, error: null }));
    try {
      const health = await bridgeFetch("/health");
      const acc = await bridgeFetch("/account");
      setBridgeAccount(acc);
      setBridgeStatus({ checking: false, connected: !!health.ok, isDemo: !!health.isDemo, allowReal: !!health.allowReal, error: null });
    } catch (e) {
      setBridgeStatus({ checking: false, connected: false, isDemo: false, allowReal: false, error: e.message });
    }
  }, [bridgeConfig, bridgeFetch]);

  useEffect(() => {
    if (!bridgeConfig.url || !bridgeConfig.key) return;
    checkBridge();
    const t = setInterval(async () => {
      try {
        const acc = await bridgeFetch("/account");
        setBridgeAccount(acc);
        const pos = await bridgeFetch("/positions");
        setBridgePositions(pos);
        setBridgeStatus((s) => ({ ...s, connected: true, isDemo: !!acc.isDemo, error: null }));
      } catch (e) {
        setBridgeStatus((s) => ({ ...s, connected: false, error: e.message }));
      }
    }, 15_000);
    return () => clearInterval(t);
  }, [bridgeConfig, bridgeFetch, checkBridge]);

  /* ---------- load persisted demo account ---------- */
  useEffect(() => {
    try {
      const raw = localStorage.getItem("demo-account");
      if (raw) {
        setAccount(JSON.parse(raw));
      } else {
        setAccount(freshAccount(DEFAULT_BALANCE_IDR));
      }
    } catch {
      setAccount(freshAccount(DEFAULT_BALANCE_IDR));
    } finally {
      setStorageReady(true);
    }
  }, []);

  function freshAccount(initialBalance) {
    return {
      initialBalance,
      balance: initialBalance,
      positions: [],
      history: [],
      dayKey: new Date().toISOString().slice(0, 10),
      dayStartBalance: initialBalance,
      consecutiveLosses: 0,
      dailyStopped: false,
    };
  }

  const persistAccount = useCallback(async (next) => {
    setAccount(next);
    try {
      localStorage.setItem("demo-account", JSON.stringify(next));
    } catch (e) {
      console.error("gagal menyimpan akun demo", e);
    }
  }, []);

  /* ---------- fetch spot price ---------- */
  const fetchSpot = useCallback(async () => {
    try {
      const res = await fetch(`${SPOT_URL}&fresh=${Date.now()}`);
      const data = await res.json();
      if (!res.ok) {
        setFetchError(data.error || `HTTP ${res.status}`);
        setConnState("OFFLINE");
        return;
      }
      setFetchError(null);
      setSpot(data);
      const ageSec = data?.data_state?.age_seconds ?? 0;
      const status = data?.data_state?.status ?? "unavailable";
      if (status === "unavailable") setConnState("OFFLINE");
      else if (status === "stale" || ageSec > STALE_AFTER_SEC) {
        setConnState(ageSec > OFFLINE_AFTER_SEC ? "OFFLINE" : "DELAYED");
      } else setConnState("LIVE");

      const priceUsd = data.spot_usd_oz;
      if (priceUsd) {
        liveSamplesRef.current.push({ t: Date.now(), p: priceUsd });
        if (liveSamplesRef.current.length > 5000) liveSamplesRef.current.shift();
        setRawPoints((prev) => mergePoints(prev, liveSamplesRef.current));
      }
    } catch (e) {
      setFetchError(e.message || "Network error");
      setConnState("OFFLINE");
    }
  }, []);

  function mergePoints(prev, liveSamples) {
    // dedupe by timestamp bucket (second)
    const map = new Map(prev.map((pt) => [pt.t, pt]));
    for (const s of liveSamples) map.set(s.t, s);
    return Array.from(map.values()).sort((a, b) => a.t - b.t);
  }

  /* ---------- fetch intraday (2-min real samples, up to 48h) once + refresh periodically ---------- */
  const fetchIntraday = useCallback(async () => {
    try {
      const res = await fetch(`${INTRADAY_URL}&fresh=${Date.now()}`);
      const data = await res.json();
      if (res.ok && Array.isArray(data.points)) {
        const pts = data.points.map((pt) => ({ t: new Date(pt.t).getTime(), p: pt.p }));
        setRawPoints((prev) => mergePoints(pts, liveSamplesRef.current));
      }
    } catch (e) {
      /* diam-diam gagal, tetap pakai live-polled points saja */
    }
  }, []);

  const fetchHistory = useCallback(async () => {
    try {
      const res = await fetch(`${HISTORY_URL}?fresh=${Date.now()}`);
      const data = await res.json();
      if (res.ok && Array.isArray(data.points)) {
        let prevClose = null;
        const candles = data.points.map((pt) => {
          const open = prevClose ?? pt.c;
          prevClose = pt.c;
          return { time: new Date(pt.d).getTime(), open, high: pt.h, low: pt.l, close: pt.c };
        });
        setHistoryDaily(candles);
      }
    } catch (e) {
      /* history opsional untuk timeframe 1D */
    }
  }, []);

  useEffect(() => {
    fetchSpot();
    fetchIntraday();
    fetchHistory();
    pollRef.current = setInterval(fetchSpot, 30_000);
    const intradayTimer = setInterval(fetchIntraday, 5 * 60_000);
    return () => {
      clearInterval(pollRef.current);
      clearInterval(intradayTimer);
    };
  }, [fetchSpot, fetchIntraday, fetchHistory]);

  /* ---------- build candles for selected timeframe ---------- */
  const tfMinutes = TIMEFRAMES.find((t) => t.key === timeframe).minutes;
  const candles = useMemo(() => {
    if (timeframe === "1D" && historyDaily.length) return historyDaily.slice(-180);
    return aggregateCandles(rawPoints, tfMinutes).slice(-180);
  }, [rawPoints, historyDaily, timeframe, tfMinutes]);

  /* ---------- higher timeframe candles for multi-TF trend ---------- */
  const candles1H = useMemo(() => aggregateCandles(rawPoints, 60), [rawPoints]);
  const candles4H = useMemo(() => aggregateCandles(rawPoints, 240), [rawPoints]);

  /* ---------- analysis engine ---------- */
  const analysis = useMemo(
    () => runAnalysis(candles, candles1H, candles4H, spot?.spot_usd_oz),
    [candles, candles1H, candles4H, spot]
  );

  /* ---------- failsafe: is trading currently allowed? ---------- */
  const dataOk = connState === "LIVE" && candles.length >= 30;
  const failReasons = [];
  if (connState === "OFFLINE") failReasons.push("Data harga OFFLINE — sumber market data terputus.");
  if (connState === "DELAYED") failReasons.push("Data harga DELAYED — menunggu update terbaru.");
  if (candles.length < 30) failReasons.push("Candle historis belum cukup untuk menghitung indikator secara valid.");
  if (botStopped) failReasons.push("Bot dihentikan manual lewat tombol EMERGENCY STOP.");
  if (account?.dailyStopped) failReasons.push("Batas rugi harian (2%) tercapai — trading dihentikan sampai hari trading berikutnya.");
  if (account?.consecutiveLosses >= MAX_CONSECUTIVE_LOSSES) failReasons.push("3 posisi berturut-turut loss — auto trading dijeda.");
  if (account && account.positions.length >= MAX_OPEN_POSITIONS) failReasons.push(`Sudah mencapai batas maksimum ${MAX_OPEN_POSITIONS} posisi terbuka.`);

  const canOpenNewTrade = dataOk && failReasons.length === 0;

  /* ---------- reset harian & mark-to-market posisi terbuka ---------- */
  useEffect(() => {
    if (!account || !spot?.spot_usd_oz) return;
    const today = new Date().toISOString().slice(0, 10);
    let next = account;
    if (account.dayKey !== today) {
      next = { ...account, dayKey: today, dayStartBalance: account.balance, dailyStopped: false };
    }
    const dailyLossPct = (next.dayStartBalance - equity(next, spot.spot_usd_oz, spot.fx_rate)) / next.dayStartBalance;
    if (dailyLossPct >= MAX_DAILY_LOSS_PCT && !next.dailyStopped) {
      next = { ...next, dailyStopped: true };
    }
    if (next !== account) persistAccount(next);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [spot]);

  /* ---------- auto trading: buka posisi kalau semua syarat terpenuhi ---------- */
  useEffect(() => {
    if (!autoTrading || !canOpenNewTrade || !account || !spot?.spot_usd_oz) return;
    if (analysis.signal !== "BUY" && analysis.signal !== "SELL") return;
    if (analysis.confidence < MIN_CONFIDENCE_TO_TRADE) return;
    openPosition(analysis.signal);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [analysis.signal, analysis.confidence, autoTrading, canOpenNewTrade, spot]);

  function equity(acc, priceUsd, fxRate) {
    let floating = 0;
    for (const p of acc.positions) {
      const diff = p.direction === "BUY" ? priceUsd - p.entryUsd : p.entryUsd - priceUsd;
      floating += diff * p.oz * fxRate;
    }
    return acc.balance + floating;
  }

  async function openPosition(direction) {
    if (!account || !spot?.spot_usd_oz || !analysis.entry) return;
    const fxRate = spot.fx_rate || spot.xau?.price / spot.spot_usd_oz;
    const riskIdr = account.balance * RISK_PER_TRADE;
    const slDistanceUsd = Math.abs(analysis.entry - analysis.stopLoss);
    if (slDistanceUsd <= 0) return;
    const oz = riskIdr / (slDistanceUsd * fxRate);

    if (bridgeConnected) {
      try {
        await bridgeFetch("/trade/open", {
          method: "POST",
          body: JSON.stringify({ direction, volumeOz: oz, stopLoss: analysis.stopLoss, takeProfit: analysis.takeProfit }),
        });
      } catch (e) {
        setBridgeStatus((s) => ({ ...s, error: `Order ditolak bridge: ${e.message}` }));
      }
      return; // posisi & balance akan ter-refresh dari poll /account & /positions
    }

    const position = {
      id: `${Date.now()}`,
      direction,
      entryUsd: analysis.entry,
      slUsd: analysis.stopLoss,
      tpUsd: analysis.takeProfit,
      oz,
      confidence: analysis.confidence,
      timeframe,
      reason: analysis.reasons.slice(0, 3).join("; "),
      openedAt: nowIso(),
      indicatorsAtEntry: { rsi: analysis.rsiVal, trend: analysis.trend, structure: analysis.structure },
    };
    persistAccount({ ...account, positions: [...account.positions, position] });
  }

  async function closePosition(id, reason) {
    if (bridgeConnected) {
      try {
        await bridgeFetch(`/trade/close/${id}`, { method: "POST" });
      } catch (e) {
        setBridgeStatus((s) => ({ ...s, error: `Gagal tutup posisi di bridge: ${e.message}` }));
      }
      return;
    }
    if (!account || !spot?.spot_usd_oz) return;
    const fxRate = spot.fx_rate || spot.xau?.price / spot.spot_usd_oz;
    const pos = account.positions.find((p) => p.id === id);
    if (!pos) return;
    const diffUsd = pos.direction === "BUY" ? spot.spot_usd_oz - pos.entryUsd : pos.entryUsd - spot.spot_usd_oz;
    const plIdr = diffUsd * pos.oz * fxRate;
    const closedTrade = {
      ...pos,
      closedAt: nowIso(),
      exitUsd: spot.spot_usd_oz,
      plIdr,
      reasonForExit: reason,
    };
    const consecutiveLosses = plIdr < 0 ? account.consecutiveLosses + 1 : 0;
    persistAccount({
      ...account,
      balance: account.balance + plIdr,
      positions: account.positions.filter((p) => p.id !== id),
      history: [closedTrade, ...account.history].slice(0, 200),
      consecutiveLosses,
    });
  }

  // auto-check TP/SL setiap tick harga
  useEffect(() => {
    if (!account || !spot?.spot_usd_oz || account.positions.length === 0) return;
    for (const p of account.positions) {
      const hitTp = p.direction === "BUY" ? spot.spot_usd_oz >= p.tpUsd : spot.spot_usd_oz <= p.tpUsd;
      const hitSl = p.direction === "BUY" ? spot.spot_usd_oz <= p.slUsd : spot.spot_usd_oz >= p.slUsd;
      if (hitTp) { closePosition(p.id, "Take Profit tercapai"); break; }
      if (hitSl) { closePosition(p.id, "Stop Loss tercapai"); break; }
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [spot]);

  if (!storageReady || !account) {
    return <div style={styles.loadingScreen}>Memuat akun demo…</div>;
  }

  const fxRate = spot?.fx_rate || (spot?.xau?.price && spot?.spot_usd_oz ? spot.xau.price / spot.spot_usd_oz : 16300);
  const eq = spot?.spot_usd_oz ? equity(account, spot.spot_usd_oz, fxRate) : account.balance;
  const floatingPl = eq - account.balance;
  const closedTrades = account.history;
  const wins = closedTrades.filter((t) => t.plIdr > 0).length;
  const losses = closedTrades.filter((t) => t.plIdr <= 0).length;
  const winRate = closedTrades.length ? (wins / closedTrades.length) * 100 : 0;
  const grossProfit = closedTrades.filter((t) => t.plIdr > 0).reduce((s, t) => s + t.plIdr, 0);
  const grossLoss = Math.abs(closedTrades.filter((t) => t.plIdr < 0).reduce((s, t) => s + t.plIdr, 0));
  const profitFactor = grossLoss > 0 ? grossProfit / grossLoss : grossProfit > 0 ? Infinity : 0;
  const totalPl = account.balance + floatingPl - account.initialBalance;

  return (
    <div style={styles.app}>
      <style>{`
        table th, table td { padding: 5px 8px; border-bottom: 1px solid #131a26; text-align: left; }
        table th { color: #64748b; font-weight: 600; text-transform: uppercase; font-size: 10px; }
        code { background: #131a26; padding: 1px 5px; border-radius: 3px; font-size: 10px; }
        @media (max-width: 860px) {
          .mainGridResponsive { grid-template-columns: 1fr !important; }
        }
      `}</style>
      <TopBar
        spot={spot}
        connState={connState}
        fetchError={fetchError}
        fxRate={fxRate}
        botStopped={botStopped}
        onEmergencyStop={() => setBotStopped((s) => !s)}
      />

      {bridgeIsRealMoney && (
        <div style={{ ...styles.failsafeBanner, background: "#3a2410", borderColor: "#f97316", color: "#fdba74" }}>
          <strong>⚠️ AKUN REAL AKTIF:</strong> Semua order lewat bridge ini akan dieksekusi dengan uang sungguhan di akun MT5 Anda (dibatasi volume maks per order oleh server). Pastikan Auto Trading hanya dinyalakan setelah Anda benar-benar yakin.
        </div>
      )}

      {failReasons.length > 0 && (
        <div style={styles.failsafeBanner}>
          <strong>⚠ TIDAK MEMBUKA POSISI BARU:</strong> {failReasons.join(" ")}
        </div>
      )}

      <div className="mainGridResponsive" style={styles.mainGrid}>
        <div style={styles.leftCol}>
          <ChartPanel candles={candles} analysis={analysis} timeframe={timeframe} setTimeframe={setTimeframe} />
          <IndicatorPanels analysis={analysis} />
        </div>

        <div style={styles.rightCol}>
          <AnalysisPanel analysis={analysis} canOpenNewTrade={canOpenNewTrade} />
          <AutoTradingPanel
            autoTrading={autoTrading}
            setAutoTrading={setAutoTrading}
            canOpenNewTrade={canOpenNewTrade}
            analysis={analysis}
            onManualOpen={() => openPosition(analysis.signal)}
          />
          <AccountPanel
            account={account}
            eq={eq}
            floatingPl={floatingPl}
            totalPl={totalPl}
            winRate={winRate}
            profitFactor={profitFactor}
            closedCount={closedTrades.length}
            bridgeConnected={bridgeConnected}
            bridgeAccount={bridgeAccount}
          />
          <BrokerBridgePanel
            bridgeConfig={bridgeConfig}
            saveBridgeConfig={saveBridgeConfig}
            bridgeStatus={bridgeStatus}
            bridgeAccount={bridgeAccount}
            checkBridge={checkBridge}
          />
        </div>
      </div>

      <PositionsAndJournal
        account={account}
        spot={spot}
        fxRate={fxRate}
        onClose={closePosition}
        bridgeConnected={bridgeConnected}
        bridgePositions={bridgePositions}
      />
    </div>
  );
}

/* ============================== ANALYSIS ENGINE ============================== */
function trendOf(candles) {
  if (candles.length < 60) return { dir: "Unclear", emaAligned: false, priceAboveEma200: false };
  const closes = candles.map((c) => c.close);
  const e20 = ema(closes, 20), e50 = ema(closes, 50), e200 = ema(closes, Math.min(200, closes.length - 1));
  const last = closes.length - 1;
  const bullish = e20[last] > e50[last] && closes[last] > e200[last];
  const bearish = e20[last] < e50[last] && closes[last] < e200[last];
  return {
    dir: bullish ? "Bullish" : bearish ? "Bearish" : "Sideways",
    emaAligned: bullish || bearish,
    priceAboveEma200: closes[last] > e200[last],
    e20: e20[last], e50: e50[last], e200: e200[last],
  };
}

function runAnalysis(candles, candles1H, candles4H, livePriceUsd) {
  const empty = {
    trend: "Belum cukup data", structure: "-", momentum: "-", signal: "NO TRADE",
    confidence: 0, entry: null, stopLoss: null, takeProfit: null, rr: null,
    reasons: ["Menunggu data candle terkumpul untuk menghitung indikator."],
    checklist: [], rsiVal: null, macdVal: null, atrVal: null, support: null, resistance: null,
  };
  if (candles.length < 30) return empty;

  const closes = candles.map((c) => c.close);
  const price = livePriceUsd || closes[closes.length - 1];
  const e20series = ema(closes, 20), e50series = ema(closes, 50), e200series = ema(closes, Math.min(200, closes.length - 1));
  const last = closes.length - 1;
  const rsiSeries = rsi(closes, 14);
  const rsiVal = rsiSeries[last];
  const macdRes = macd(closes);
  const macdHist = macdRes.hist[last];
  const atrSeries = atr(candles, 14);
  const atrVal = atrSeries[last];
  const { highs, lows } = findSwings(candles, 3);
  const resistance = highs.length ? highs[highs.length - 1].price : Math.max(...candles.slice(-30).map((c) => c.high));
  const support = lows.length ? lows[lows.length - 1].price : Math.min(...candles.slice(-30).map((c) => c.low));

  // market structure dari 2 swing high & 2 swing low terakhir
  let structure = "Ranging / tidak jelas";
  if (highs.length >= 2 && lows.length >= 2) {
    const hh = highs[highs.length - 1].price > highs[highs.length - 2].price;
    const hl = lows[lows.length - 1].price > lows[lows.length - 2].price;
    const lh = highs[highs.length - 1].price < highs[highs.length - 2].price;
    const ll = lows[lows.length - 1].price < lows[lows.length - 2].price;
    if (hh && hl) structure = "Higher High + Higher Low (Bullish)";
    else if (lh && ll) structure = "Lower High + Lower Low (Bearish)";
  }

  const ltfTrend = trendOf(candles);
  const htf1H = trendOf(candles1H);
  const htf4H = trendOf(candles4H);
  const higherTfBullish = htf1H.dir === "Bullish" && htf4H.dir === "Bullish";
  const higherTfBearish = htf1H.dir === "Bearish" && htf4H.dir === "Bearish";

  const momentumBullish = rsiVal > 50 && macdHist > 0;
  const momentumBearish = rsiVal < 50 && macdHist < 0;
  const rsiExtreme = rsiVal > 80 || rsiVal < 20;
  const volatilityOk = atrVal > 0 && atrVal / price < 0.03; // ATR wajar, bukan ekstrem

  const nearSupport = Math.abs(price - support) / price < 0.004;
  const nearResistance = Math.abs(price - resistance) / price < 0.004;

  // ---- checklist BUY ----
  const buyChecklist = [
    { label: "Higher timeframe (1H & 4H) bullish", pass: higherTfBullish },
    { label: "Harga di atas EMA 200", pass: price > e200series[last] },
    { label: "EMA 20 > EMA 50", pass: e20series[last] > e50series[last] },
    { label: "Market structure bullish", pass: structure.includes("Bullish") },
    { label: "Retest support valid", pass: nearSupport },
    { label: "Momentum bullish (RSI>50 & MACD histogram positif)", pass: momentumBullish },
    { label: "RSI tidak overbought ekstrem", pass: rsiVal < 80 },
    { label: "Volatilitas (ATR) wajar", pass: volatilityOk },
  ];
  const sellChecklist = [
    { label: "Higher timeframe (1H & 4H) bearish", pass: higherTfBearish },
    { label: "Harga di bawah EMA 200", pass: price < e200series[last] },
    { label: "EMA 20 < EMA 50", pass: e20series[last] < e50series[last] },
    { label: "Market structure bearish", pass: structure.includes("Bearish") },
    { label: "Retest resistance valid", pass: nearResistance },
    { label: "Momentum bearish (RSI<50 & MACD histogram negatif)", pass: momentumBearish },
    { label: "RSI tidak oversold ekstrem", pass: rsiVal > 20 },
    { label: "Volatilitas (ATR) wajar", pass: volatilityOk },
  ];
  const buyScore = buyChecklist.filter((c) => c.pass).length;
  const sellScore = sellChecklist.filter((c) => c.pass).length;

  let direction = null;
  if (buyScore >= 6 && buyScore > sellScore) direction = "BUY";
  else if (sellScore >= 6 && sellScore > buyScore) direction = "SELL";

  const entry = price;
  const slDist = Math.max(atrVal * 1.5, price * 0.002);
  const stopLoss = direction === "BUY" ? entry - slDist : direction === "SELL" ? entry + slDist : null;
  const takeProfit = direction === "BUY" ? entry + slDist * 2.5 : direction === "SELL" ? entry - slDist * 2.5 : null;
  const rr = stopLoss && takeProfit ? Math.abs(takeProfit - entry) / Math.abs(entry - stopLoss) : null;

  // ---- confidence scoring 0-100 sesuai bobot spesifikasi ----
  let confidence = 0;
  const trendAligned = direction === "BUY" ? higherTfBullish : direction === "SELL" ? higherTfBearish : false;
  const structAligned = direction === "BUY" ? structure.includes("Bullish") : direction === "SELL" ? structure.includes("Bearish") : false;
  const momentumAligned = direction === "BUY" ? momentumBullish : direction === "SELL" ? momentumBearish : false;
  const srAligned = direction === "BUY" ? nearSupport : direction === "SELL" ? nearResistance : false;
  const emaAligned = direction === "BUY" ? e20series[last] > e50series[last] : direction === "SELL" ? e20series[last] < e50series[last] : false;
  if (direction) {
    confidence += trendAligned ? 20 : 0;
    confidence += structAligned ? 20 : 0;
    confidence += momentumAligned ? 15 : 0;
    confidence += srAligned ? 15 : 0;
    confidence += emaAligned ? 10 : 0;
    confidence += !rsiExtreme ? 5 : 0;
    confidence += (direction === "BUY" ? macdHist > 0 : macdHist < 0) ? 5 : 0;
    confidence += volatilityOk ? 5 : 0;
    confidence += rr && rr >= 2 ? 5 : 0;
  }

  const reasons = [];
  if (direction) {
    if (trendAligned) reasons.push("Higher timeframe (1H & 4H) selaras dengan arah sinyal");
    if (structAligned) reasons.push(`Market structure: ${structure}`);
    if (momentumAligned) reasons.push("Momentum RSI & MACD mendukung arah sinyal");
    if (srAligned) reasons.push(direction === "BUY" ? "Retest support berhasil" : "Retest resistance berhasil");
    if (emaAligned) reasons.push("Susunan EMA 20/50 mendukung arah sinyal");
    if (rr) reasons.push(`Risk/Reward ≈ 1:${rr.toFixed(1)}`);
  } else {
    reasons.push("Kondisi checklist BUY dan SELL tidak dominan salah satu — sinyal bertentangan atau lemah.");
  }

  const signal = direction && confidence >= MIN_CONFIDENCE_TO_TRADE ? direction : "NO TRADE";

  return {
    trend: ltfTrend.dir, htf1H: htf1H.dir, htf4H: htf4H.dir,
    structure, momentum: momentumBullish ? "Bullish" : momentumBearish ? "Bearish" : "Netral",
    signal, direction, confidence,
    entry: direction ? entry : null,
    stopLoss, takeProfit, rr,
    reasons, checklist: direction === "SELL" ? sellChecklist : buyChecklist,
    rsiVal, macdHist, atrVal, support, resistance,
    e20: e20series[last], e50: e50series[last], e200: e200series[last],
    rsiSeries, macdRes, atrSeries, candles,
  };
}

/* ================================ UI PARTS ================================ */
function TopBar({ spot, connState, fetchError, fxRate, botStopped, onEmergencyStop }) {
  const color = connState === "LIVE" ? "#22c55e" : connState === "DELAYED" ? "#eab308" : "#ef4444";
  const dot = connState === "LIVE" ? "🟢" : connState === "DELAYED" ? "🟡" : "🔴";
  const priceUsd = spot?.spot_usd_oz;
  const priceIdr = spot?.xau?.price;
  const spreadNote = "N/A (feed mid-market, bukan bid/ask broker)";
  const ageSec = spot?.data_state?.age_seconds;

  return (
    <div style={styles.topBar}>
      <div style={styles.topBarLeft}>
        <div style={{ fontWeight: 700, fontSize: 18, letterSpacing: 0.5 }}>XAUUSD · DEMO</div>
        <div style={{ ...styles.statusPill, color, borderColor: color }}>{dot} {connState}</div>
      </div>
      <div style={styles.topBarPrices}>
        <PriceCell label="XAU/USD" value={priceUsd ? fmtUSD(priceUsd) : "—"} big />
        <PriceCell label="XAU/IDR (per oz)" value={priceIdr ? fmtIDR(priceIdr) : "—"} />
        <PriceCell label="Spread" value={spreadNote} small />
        <PriceCell label="Update terakhir" value={spot?.updated_at ? new Date(spot.updated_at).toLocaleTimeString("id-ID") : "—"} small />
        <PriceCell label="Latency data" value={ageSec != null ? `${ageSec}s` : "—"} small />
      </div>
      <button style={{ ...styles.stopBtn, background: botStopped ? "#7f1d1d" : "#dc2626" }} onClick={onEmergencyStop}>
        {botStopped ? "BOT DIHENTIKAN — Aktifkan lagi" : "🛑 EMERGENCY STOP"}
      </button>
      {fetchError && <div style={styles.errorLine}>Gagal ambil data: {fetchError}</div>}
    </div>
  );
}
function PriceCell({ label, value, big, small }) {
  return (
    <div style={styles.priceCell}>
      <div style={styles.priceLabel}>{label}</div>
      <div style={{ fontWeight: big ? 700 : 600, fontSize: big ? 20 : small ? 12 : 14, fontFamily: "ui-monospace, monospace" }}>{value}</div>
    </div>
  );
}

function ChartPanel({ candles, analysis, timeframe, setTimeframe }) {
  const W = 760, H = 340, padL = 50, padR = 70, padT = 16, padB = 24;
  if (candles.length < 2) {
    return (
      <div style={styles.panel}>
        <TfSelector timeframe={timeframe} setTimeframe={setTimeframe} />
        <div style={styles.chartEmpty}>Mengumpulkan candle realtime… chart akan mulai tergambar begitu cukup data tick terkumpul.</div>
      </div>
    );
  }
  const highs = candles.map((c) => c.high), lows = candles.map((c) => c.low);
  const max = Math.max(...highs, analysis.resistance || -Infinity);
  const min = Math.min(...lows, analysis.support || Infinity);
  const range = max - min || 1;
  const x = (i) => padL + (i / (candles.length - 1)) * (W - padL - padR);
  const y = (v) => padT + (1 - (v - min) / range) * (H - padT - padB);
  const cw = Math.max(2, ((W - padL - padR) / candles.length) * 0.6);

  return (
    <div style={styles.panel}>
      <TfSelector timeframe={timeframe} setTimeframe={setTimeframe} />
      <svg width="100%" viewBox={`0 0 ${W} ${H}`} style={{ background: "#0b0f17", borderRadius: 8 }}>
        {[0, 0.25, 0.5, 0.75, 1].map((f) => (
          <line key={f} x1={padL} x2={W - padR} y1={padT + f * (H - padT - padB)} y2={padT + f * (H - padT - padB)} stroke="#1c2431" strokeWidth="1" />
        ))}
        {analysis.support && (
          <g>
            <line x1={padL} x2={W - padR} y1={y(analysis.support)} y2={y(analysis.support)} stroke="#22c55e" strokeDasharray="4 3" strokeWidth="1" />
            <text x={W - padR + 4} y={y(analysis.support) + 3} fill="#22c55e" fontSize="10">S {analysis.support.toFixed(1)}</text>
          </g>
        )}
        {analysis.resistance && (
          <g>
            <line x1={padL} x2={W - padR} y1={y(analysis.resistance)} y2={y(analysis.resistance)} stroke="#ef4444" strokeDasharray="4 3" strokeWidth="1" />
            <text x={W - padR + 4} y={y(analysis.resistance) + 3} fill="#ef4444" fontSize="10">R {analysis.resistance.toFixed(1)}</text>
          </g>
        )}
        {analysis.entry && analysis.stopLoss && (
          <>
            <line x1={padL} x2={W - padR} y1={y(analysis.entry)} y2={y(analysis.entry)} stroke="#60a5fa" strokeWidth="1" strokeDasharray="2 2" />
            <line x1={padL} x2={W - padR} y1={y(analysis.stopLoss)} y2={y(analysis.stopLoss)} stroke="#f87171" strokeWidth="1" strokeDasharray="2 2" />
            <line x1={padL} x2={W - padR} y1={y(analysis.takeProfit)} y2={y(analysis.takeProfit)} stroke="#4ade80" strokeWidth="1" strokeDasharray="2 2" />
          </>
        )}
        {candles.map((c, i) => {
          const up = c.close >= c.open;
          const col = up ? "#22c55e" : "#ef4444";
          return (
            <g key={c.time}>
              <line x1={x(i)} x2={x(i)} y1={y(c.high)} y2={y(c.low)} stroke={col} strokeWidth="1" />
              <rect x={x(i) - cw / 2} y={y(Math.max(c.open, c.close))} width={cw} height={Math.max(1, Math.abs(y(c.open) - y(c.close)))} fill={col} />
            </g>
          );
        })}
        <text x={padL} y={H - 6} fill="#64748b" fontSize="10">{new Date(candles[0].time).toLocaleString("id-ID")}</text>
        <text x={W - padR - 90} y={H - 6} fill="#64748b" fontSize="10">{new Date(candles[candles.length - 1].time).toLocaleString("id-ID")}</text>
      </svg>
      <div style={styles.legendRow}>
        <Legend color="#60a5fa" label="Entry" /> <Legend color="#f87171" label="Stop Loss" /> <Legend color="#4ade80" label="Take Profit" />
        <Legend color="#22c55e" label="Support" /> <Legend color="#ef4444" label="Resistance" />
      </div>
    </div>
  );
}
function Legend({ color, label }) {
  return <span style={{ fontSize: 11, color: "#94a3b8", marginRight: 12 }}><span style={{ display: "inline-block", width: 8, height: 8, background: color, marginRight: 4, borderRadius: 2 }} />{label}</span>;
}
function TfSelector({ timeframe, setTimeframe }) {
  return (
    <div style={{ display: "flex", gap: 6, marginBottom: 8, flexWrap: "wrap" }}>
      {TIMEFRAMES.map((t) => (
        <button key={t.key} onClick={() => setTimeframe(t.key)} style={{ ...styles.tfBtn, ...(timeframe === t.key ? styles.tfBtnActive : {}) }}>{t.label}</button>
      ))}
    </div>
  );
}

function IndicatorPanels({ analysis }) {
  return (
    <div style={styles.panel}>
      <div style={styles.sectionTitle}>Indikator</div>
      <div style={styles.indicatorGrid}>
        <IndVal label="RSI (14)" value={analysis.rsiVal ? analysis.rsiVal.toFixed(1) : "—"} warn={analysis.rsiVal > 70 || analysis.rsiVal < 30} />
        <IndVal label="MACD Histogram" value={analysis.macdHist ? analysis.macdHist.toFixed(2) : "—"} />
        <IndVal label="ATR (14)" value={analysis.atrVal ? analysis.atrVal.toFixed(2) : "—"} />
        <IndVal label="EMA 20" value={analysis.e20 ? analysis.e20.toFixed(2) : "—"} />
        <IndVal label="EMA 50" value={analysis.e50 ? analysis.e50.toFixed(2) : "—"} />
        <IndVal label="EMA 200" value={analysis.e200 ? analysis.e200.toFixed(2) : "—"} />
      </div>
    </div>
  );
}
function IndVal({ label, value, warn }) {
  return (
    <div style={styles.indCell}>
      <div style={styles.priceLabel}>{label}</div>
      <div style={{ fontFamily: "ui-monospace, monospace", color: warn ? "#eab308" : "#e2e8f0" }}>{value}</div>
    </div>
  );
}

function AnalysisPanel({ analysis, canOpenNewTrade }) {
  const sigColor = analysis.signal === "BUY" ? "#22c55e" : analysis.signal === "SELL" ? "#ef4444" : "#64748b";
  return (
    <div style={styles.panel}>
      <div style={styles.sectionTitle}>AI ANALYSIS (multi-timeframe)</div>
      <Row label="TREND (chart aktif)" value={analysis.trend} />
      <Row label="HTF 1H / 4H" value={`${analysis.htf1H || "-"} / ${analysis.htf4H || "-"}`} />
      <Row label="STRUCTURE" value={analysis.structure} />
      <Row label="MOMENTUM" value={analysis.momentum} />
      <div style={{ ...styles.signalBox, borderColor: sigColor }}>
        <div style={{ fontSize: 22, fontWeight: 800, color: sigColor }}>{analysis.signal}</div>
        <div style={styles.priceLabel}>Confidence: {analysis.confidence}% {analysis.confidence < MIN_CONFIDENCE_TO_TRADE && analysis.direction && "(di bawah threshold 85%, tidak dieksekusi)"}</div>
      </div>
      <div style={{ fontSize: 10, color: "#64748b", marginBottom: 8 }}>
        Confidence adalah skor model dari kombinasi indikator, BUKAN jaminan probabilitas profit 85%. Tidak ada guarantee win rate.
      </div>
      {analysis.entry && (
        <>
          <Row label="ENTRY" value={fmtUSD(analysis.entry)} />
          <Row label="STOP LOSS" value={fmtUSD(analysis.stopLoss)} />
          <Row label="TAKE PROFIT" value={fmtUSD(analysis.takeProfit)} />
          <Row label="RISK/REWARD" value={analysis.rr ? `1:${analysis.rr.toFixed(1)}` : "-"} />
        </>
      )}
      <div style={styles.sectionTitle}>REASON</div>
      <ul style={{ margin: "4px 0", paddingLeft: 18, fontSize: 12, color: "#cbd5e1" }}>
        {analysis.reasons.map((r, i) => <li key={i}>{r}</li>)}
      </ul>
      {analysis.checklist?.length > 0 && (
        <details>
          <summary style={{ fontSize: 12, color: "#94a3b8", cursor: "pointer" }}>Lihat checklist kondisi lengkap</summary>
          <ul style={{ margin: "4px 0", paddingLeft: 18, fontSize: 12 }}>
            {analysis.checklist.map((c, i) => (
              <li key={i} style={{ color: c.pass ? "#4ade80" : "#64748b" }}>{c.pass ? "✔" : "✘"} {c.label}</li>
            ))}
          </ul>
        </details>
      )}
    </div>
  );
}
function Row({ label, value }) {
  return (
    <div style={styles.row}>
      <span style={styles.priceLabel}>{label}</span>
      <span style={{ fontFamily: "ui-monospace, monospace", fontSize: 12 }}>{value}</span>
    </div>
  );
}

function AutoTradingPanel({ autoTrading, setAutoTrading, canOpenNewTrade, analysis, onManualOpen }) {
  const canManual = canOpenNewTrade && analysis.direction && analysis.confidence >= MIN_CONFIDENCE_TO_TRADE;
  return (
    <div style={styles.panel}>
      <div style={styles.row}>
        <div style={styles.sectionTitle}>AUTO TRADING</div>
        <button onClick={() => setAutoTrading((v) => !v)} style={{ ...styles.toggleBtn, background: autoTrading ? "#16a34a" : "#334155" }}>
          {autoTrading ? "ON" : "OFF"}
        </button>
      </div>
      <div style={{ fontSize: 11, color: "#94a3b8", marginBottom: 8 }}>
        Bot hanya membuka posisi DEMO otomatis jika confidence ≥ {MIN_CONFIDENCE_TO_TRADE}% dan semua failsafe hijau. Tidak ada trade dipaksakan.
      </div>
      <button disabled={!canManual} onClick={onManualOpen} style={{ ...styles.manualBtn, opacity: canManual ? 1 : 0.4 }}>
        Buka posisi manual sesuai sinyal saat ini
      </button>
    </div>
  );
}

function AccountPanel({ account, eq, floatingPl, totalPl, winRate, profitFactor, closedCount, bridgeConnected, bridgeAccount }) {
  if (bridgeConnected && bridgeAccount) {
    return (
      <div style={styles.panel}>
        <div style={styles.sectionTitle}>MT5 DEMO ACCOUNT (live dari bridge)</div>
        <Row label="Login / Server" value={`${bridgeAccount.login} @ ${bridgeAccount.server}`} />
        <Row label="Balance" value={`${bridgeAccount.balance?.toLocaleString("id-ID")} ${bridgeAccount.currency}`} />
        <Row label="Equity" value={`${bridgeAccount.equity?.toLocaleString("id-ID")} ${bridgeAccount.currency}`} />
        <Row label="Margin terpakai" value={`${bridgeAccount.margin?.toLocaleString("id-ID")} ${bridgeAccount.currency}`} />
        <Row label="Free margin" value={`${bridgeAccount.freeMargin?.toLocaleString("id-ID")} ${bridgeAccount.currency}`} />
        <Row label="Risk / trade" value={`${(RISK_PER_TRADE * 100).toFixed(1)}% saldo`} />
        <div style={{ fontSize: 10, color: "#64748b", marginTop: 6 }}>Data langsung dari akun demo MT5 Anda lewat bridge, refresh tiap 15 detik.</div>
      </div>
    );
  }
  return (
    <div style={styles.panel}>
      <div style={styles.sectionTitle}>DEMO ACCOUNT (paper trading lokal)</div>
      <Row label="Balance" value={fmtIDR(account.balance)} />
      <Row label="Equity" value={fmtIDR(eq)} />
      <Row label="Floating P/L" value={fmtIDR(floatingPl)} />
      <Row label="Total P/L" value={fmtIDR(totalPl)} />
      <Row label="Win Rate" value={`${fmtPct(winRate)} (${closedCount} trade)`} />
      <Row label="Profit Factor" value={isFinite(profitFactor) ? profitFactor.toFixed(2) : "∞"} />
      <Row label="Risk / trade" value={`${(RISK_PER_TRADE * 100).toFixed(1)}% saldo`} />
      <Row label="Max posisi terbuka" value={MAX_OPEN_POSITIONS} />
      <Row label="Max daily loss" value={`${(MAX_DAILY_LOSS_PCT * 100).toFixed(0)}%`} />
      {account.dailyStopped && <div style={styles.warnLine}>Trading dihentikan hari ini (batas rugi harian tercapai).</div>}
      {account.consecutiveLosses >= MAX_CONSECUTIVE_LOSSES && <div style={styles.warnLine}>Auto trading dijeda — 3 loss berturut-turut.</div>}
    </div>
  );
}

function BrokerBridgePanel({ bridgeConfig, saveBridgeConfig, bridgeStatus, bridgeAccount, checkBridge }) {
  const [urlDraft, setUrlDraft] = useState(bridgeConfig.url);
  const [keyDraft, setKeyDraft] = useState(bridgeConfig.key);
  useEffect(() => { setUrlDraft(bridgeConfig.url); setKeyDraft(bridgeConfig.key); }, [bridgeConfig]);

  const mode = !bridgeStatus.connected
    ? "PAPER (lokal)"
    : bridgeStatus.isDemo
    ? "MT5 DEMO (bridge)"
    : bridgeStatus.allowReal
    ? "MT5 REAL (bridge) — UANG SUNGGUHAN"
    : "PAPER (lokal)";
  const modeColor = !bridgeStatus.connected
    ? "#64748b"
    : bridgeStatus.isDemo
    ? "#22c55e"
    : bridgeStatus.allowReal
    ? "#f97316"
    : "#64748b";

  return (
    <div style={styles.panel}>
      <div style={styles.sectionTitle}>BROKER BRIDGE (MT4/MT5)</div>
      <Row label="Mode eksekusi" value={<span style={{ color: modeColor, fontWeight: 700 }}>{mode}</span>} />
      {bridgeConfig.url && (
        <Row
          label="Status"
          value={
            bridgeStatus.checking
              ? "Mengecek…"
              : !bridgeStatus.connected
              ? "Tidak terhubung"
              : bridgeStatus.isDemo
              ? "Connected · DEMO ✓"
              : bridgeStatus.allowReal
              ? "Connected · REAL (ALLOW_REAL_TRADING aktif) ⚠️"
              : "Connected tapi BUKAN demo — ditolak"
          }
        />
      )}
      <div style={{ margin: "8px 0" }}>
        <label style={styles.smallLabel}>Bridge URL</label>
        <input style={styles.input} placeholder="https://xxx.up.railway.app" value={urlDraft} onChange={(e) => setUrlDraft(e.target.value)} />
        <label style={styles.smallLabel}>Bridge Key</label>
        <input style={styles.input} placeholder="BRIDGE_API_KEY Anda" value={keyDraft} onChange={(e) => setKeyDraft(e.target.value)} type="password" />
        <button style={styles.manualBtn} onClick={async () => { await saveBridgeConfig({ url: urlDraft, key: keyDraft }); setTimeout(checkBridge, 300); }}>
          Simpan & Tes Koneksi
        </button>
      </div>
      {bridgeStatus.error && <div style={{ color: "#f87171", fontSize: 11, marginBottom: 6 }}>{bridgeStatus.error}</div>}
      <div style={{ fontSize: 11, color: "#94a3b8", lineHeight: 1.5 }}>
        Bridge adalah server kecil (kode & panduan terpisah) yang menghubungkan lewat MetaApi.cloud ke akun demo MT4/MT5 Anda —
        kredensial MT5 hanya disimpan di server itu, tidak pernah di sini. Bridge menolak semua order kalau akun yang terhubung
        terdeteksi bukan DEMO. Selama belum tersambung & terverifikasi demo, semua order tetap jalan sebagai paper trading lokal.
      </div>
    </div>
  );
}

function PositionsAndJournal({ account, spot, fxRate, onClose, bridgeConnected, bridgePositions }) {
  if (bridgeConnected) {
    return (
      <div style={{ ...styles.panel, gridColumn: "1 / -1" }}>
        <div style={styles.sectionTitle}>OPEN POSITIONS (MT5 Demo — live dari bridge)</div>
        {bridgePositions.length === 0 ? (
          <div style={styles.emptyNote}>Tidak ada posisi terbuka di akun demo.</div>
        ) : (
          <table style={styles.table}>
            <thead><tr><th>Arah</th><th>Entry</th><th>SL</th><th>TP</th><th>Volume (lot)</th><th>Profit</th><th></th></tr></thead>
            <tbody>
              {bridgePositions.map((p) => (
                <tr key={p.id}>
                  <td style={{ color: p.type === "POSITION_TYPE_BUY" ? "#22c55e" : "#ef4444" }}>{p.type === "POSITION_TYPE_BUY" ? "BUY" : "SELL"}</td>
                  <td>{fmtUSD(p.openPrice)}</td><td>{p.stopLoss ? fmtUSD(p.stopLoss) : "-"}</td><td>{p.takeProfit ? fmtUSD(p.takeProfit) : "-"}</td>
                  <td>{p.volume}</td>
                  <td style={{ color: (p.profit || 0) >= 0 ? "#4ade80" : "#f87171" }}>{p.profit != null ? p.profit.toFixed(2) : "-"}</td>
                  <td><button style={styles.closeBtn} onClick={() => onClose(p.id, "Ditutup manual (MT5)")}>Tutup</button></td>
                </tr>
              ))}
            </tbody>
          </table>
        )}
        <div style={{ fontSize: 10, color: "#64748b", marginTop: 6 }}>Journal transaksi tertutup: cek riwayat langsung di terminal MT5 Anda, atau tambahkan endpoint /history bridge ke panel ini.</div>
      </div>
    );
  }
  return (
    <div style={{ ...styles.panel, gridColumn: "1 / -1" }}>
      <div style={styles.sectionTitle}>OPEN POSITIONS</div>
      {account.positions.length === 0 ? (
        <div style={styles.emptyNote}>Tidak ada posisi terbuka.</div>
      ) : (
        <table style={styles.table}>
          <thead><tr><th>Arah</th><th>Entry</th><th>SL</th><th>TP</th><th>Lot (oz)</th><th>Floating P/L</th><th>Confidence</th><th></th></tr></thead>
          <tbody>
            {account.positions.map((p) => {
              const diffUsd = spot?.spot_usd_oz ? (p.direction === "BUY" ? spot.spot_usd_oz - p.entryUsd : p.entryUsd - spot.spot_usd_oz) : 0;
              const plIdr = diffUsd * p.oz * fxRate;
              return (
                <tr key={p.id}>
                  <td style={{ color: p.direction === "BUY" ? "#22c55e" : "#ef4444" }}>{p.direction}</td>
                  <td>{fmtUSD(p.entryUsd)}</td><td>{fmtUSD(p.slUsd)}</td><td>{fmtUSD(p.tpUsd)}</td>
                  <td>{p.oz.toFixed(3)}</td>
                  <td style={{ color: plIdr >= 0 ? "#4ade80" : "#f87171" }}>{fmtIDR(plIdr)}</td>
                  <td>{p.confidence}%</td>
                  <td><button style={styles.closeBtn} onClick={() => onClose(p.id, "Ditutup manual")}>Tutup</button></td>
                </tr>
              );
            })}
          </tbody>
        </table>
      )}

      <div style={{ ...styles.sectionTitle, marginTop: 14 }}>TRADE JOURNAL</div>
      {account.history.length === 0 ? (
        <div style={styles.emptyNote}>Belum ada transaksi tercatat.</div>
      ) : (
        <table style={styles.table}>
          <thead><tr><th>Waktu</th><th>Arah</th><th>Entry</th><th>Exit</th><th>P/L</th><th>Confidence</th><th>TF</th><th>Alasan</th></tr></thead>
          <tbody>
            {account.history.map((t) => (
              <tr key={t.id}>
                <td>{new Date(t.closedAt).toLocaleString("id-ID")}</td>
                <td style={{ color: t.direction === "BUY" ? "#22c55e" : "#ef4444" }}>{t.direction}</td>
                <td>{fmtUSD(t.entryUsd)}</td><td>{fmtUSD(t.exitUsd)}</td>
                <td style={{ color: t.plIdr >= 0 ? "#4ade80" : "#f87171" }}>{fmtIDR(t.plIdr)}</td>
                <td>{t.confidence}%</td><td>{t.timeframe}</td>
                <td style={{ fontSize: 10 }}>{t.reasonForExit} — {t.reason}</td>
              </tr>
            ))}
          </tbody>
        </table>
      )}
    </div>
  );
}

/* ================================== STYLES ================================== */
const styles = {
  app: { background: "#05070c", color: "#e2e8f0", minHeight: "100vh", fontFamily: "Inter, ui-sans-serif, system-ui", padding: 12 },
  loadingScreen: { background: "#05070c", color: "#94a3b8", minHeight: "100vh", display: "flex", alignItems: "center", justifyContent: "center" },
  topBar: { background: "#0b0f17", border: "1px solid #1c2431", borderRadius: 10, padding: 12, marginBottom: 10, display: "flex", flexWrap: "wrap", alignItems: "center", gap: 14, position: "relative" },
  topBarLeft: { display: "flex", alignItems: "center", gap: 10 },
  statusPill: { border: "1px solid", borderRadius: 20, padding: "2px 10px", fontSize: 12, fontWeight: 600 },
  topBarPrices: { display: "flex", gap: 18, flexWrap: "wrap", flex: 1 },
  priceCell: { minWidth: 90 },
  priceLabel: { fontSize: 10, color: "#64748b", textTransform: "uppercase", letterSpacing: 0.4 },
  stopBtn: { border: "none", color: "white", fontWeight: 700, fontSize: 12, padding: "8px 14px", borderRadius: 8, cursor: "pointer" },
  errorLine: { position: "absolute", bottom: -18, left: 12, fontSize: 11, color: "#f87171" },
  failsafeBanner: { background: "#3a1414", border: "1px solid #7f1d1d", color: "#fca5a5", padding: "8px 12px", borderRadius: 8, fontSize: 12, marginBottom: 10 },
  mainGrid: { display: "grid", gridTemplateColumns: "minmax(0,1fr) 340px", gap: 10 },
  leftCol: { display: "flex", flexDirection: "column", gap: 10, minWidth: 0 },
  rightCol: { display: "flex", flexDirection: "column", gap: 10 },
  panel: { background: "#0b0f17", border: "1px solid #1c2431", borderRadius: 10, padding: 12 },
  sectionTitle: { fontSize: 11, fontWeight: 700, color: "#94a3b8", letterSpacing: 0.6, marginBottom: 8, textTransform: "uppercase" },
  chartEmpty: { color: "#64748b", fontSize: 13, padding: "40px 0", textAlign: "center" },
  legendRow: { marginTop: 6 },
  tfBtn: { background: "#0f1520", border: "1px solid #1c2431", color: "#94a3b8", fontSize: 11, padding: "4px 10px", borderRadius: 6, cursor: "pointer" },
  tfBtnActive: { background: "#1d4ed8", color: "white", borderColor: "#1d4ed8" },
  indicatorGrid: { display: "grid", gridTemplateColumns: "1fr 1fr 1fr", gap: 10 },
  indCell: { background: "#0f1520", borderRadius: 6, padding: 8 },
  smallLabel: { display: "block", fontSize: 10, color: "#64748b", marginTop: 6, marginBottom: 2 },
  input: { width: "100%", boxSizing: "border-box", background: "#0f1520", border: "1px solid #1c2431", color: "#e2e8f0", borderRadius: 6, padding: "6px 8px", fontSize: 12, marginBottom: 2 },
  signalBox: { border: "2px solid", borderRadius: 8, padding: 10, textAlign: "center", margin: "8px 0" },
  row: { display: "flex", justifyContent: "space-between", padding: "4px 0", borderBottom: "1px solid #131a26" },
  toggleBtn: { border: "none", color: "white", fontWeight: 700, fontSize: 11, padding: "4px 14px", borderRadius: 20, cursor: "pointer" },
  manualBtn: { width: "100%", background: "#1d4ed8", border: "none", color: "white", padding: "8px 0", borderRadius: 6, fontSize: 12, fontWeight: 600, cursor: "pointer" },
  warnLine: { color: "#eab308", fontSize: 11, marginTop: 6 },
  emptyNote: { color: "#475569", fontSize: 12, padding: "8px 0" },
  table: { width: "100%", borderCollapse: "collapse", fontSize: 11 },
  closeBtn: { background: "#334155", border: "none", color: "#e2e8f0", fontSize: 10, padding: "3px 8px", borderRadius: 4, cursor: "pointer" },
};
