// ================================================================
// MacroPulse — app.js
// Curated by Yuvraj Sureka | IB Analyst | CFA L2 | Trading
//
// DATA SOURCES (all confirmed CORS-friendly from browsers):
//   Crypto prices/dominance  → CoinGecko public API (no key)
//   Crypto prices backup     → Binance public API   (no key)
//   FX rates (EUR,GBP,JPY,INR) → Frankfurter.app   (no key)
//   FX rates backup          → open.er-api.com      (no key)
//   Equities + yields        → Yahoo Finance via corsproxy.io
//   News                     → Reuters RSS via allorigins proxy
//   Macro calendar           → Econdb via allorigins proxy
//   India fundamentals       → World Bank API       (no key)
// ================================================================

'use strict';

// ── CONFIG ──────────────────────────────────────────────────────────
const CFG = {
  REFRESH_MS:    45000,
  CHUNK_SIZE:    4,       // symbols per concurrent Yahoo batch
  CHUNK_DELAY:   400,     // ms between batches
  FETCH_TIMEOUT: 8000,    // ms per fetch attempt
};

// ── UTILITIES ────────────────────────────────────────────────────────
const $  = id => document.getElementById(id);
const qs = sel => document.querySelector(sel);
const fmt     = (n, d=2) => (n != null && !isNaN(n)) ? Number(n).toLocaleString('en-US',{minimumFractionDigits:d,maximumFractionDigits:d}) : '—';
const fmtPct  = n => (n != null && !isNaN(n)) ? (n>=0?'+':'') + Number(n).toFixed(2) + '%' : '—';
const clr     = n => n == null ? 'flat' : n > 0 ? 'up' : n < 0 ? 'down' : 'flat';
const fillClr = n => n > 0 ? 'fill-up' : n < 0 ? 'fill-down' : '';
const sleep   = ms => new Promise(r => setTimeout(r, ms));
const shuffle = arr => { const a=[...arr]; for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];} return a; };

// ── SYMBOL REGISTRY ──────────────────────────────────────────────────
const SYM = {
  us:    ['^GSPC','^NDX','^DJI','^RUT'],
  eu:    ['^STOXX50E','^FTSE','^GDAXI'],
  asia:  ['^N225','^HSI','000001.SS','^KS11'],
  india: ['^NSEI','^NSEBANK','RELIANCE.NS','TCS.NS'],
  yield: ['^IRX','^FVX','^TNX','^TYX'],
  fx:    ['EURUSD=X','GBPUSD=X','USDJPY=X','DX-Y.NYB','USDINR=X'],
  comm:  ['GC=F','SI=F','HG=F','CL=F','BZ=F','NG=F'],
  ai_us: ['NVDA','MSFT','AMZN','GOOGL','META','AMD','AVGO'],
  ai_tw: ['TSM','2330.TW','005930.KS','000660.KS'],
  ai_jp: ['8035.T','6857.T','9984.T','BABA','TCEHY'],
};

const NAMES = {
  '^GSPC':'S&P 500','^NDX':'Nasdaq 100','^DJI':'Dow Jones','^RUT':'Russell 2000',
  '^STOXX50E':'Euro Stoxx 50','^FTSE':'FTSE 100','^GDAXI':'DAX 40',
  '^N225':'Nikkei 225','^HSI':'Hang Seng','000001.SS':'Shanghai Comp.','^KS11':'KOSPI',
  '^NSEI':'Nifty 50','^NSEBANK':'Bank Nifty','RELIANCE.NS':'Reliance Inds','TCS.NS':'TCS',
  '^IRX':'US 3M Bill','^FVX':'US 5Y Note','^TNX':'US 10Y Note','^TYX':'US 30Y Bond',
  'EURUSD=X':'EUR/USD','GBPUSD=X':'GBP/USD','USDJPY=X':'USD/JPY','DX-Y.NYB':'DXY Index','USDINR=X':'USD/INR',
  'GC=F':'Gold','SI=F':'Silver','HG=F':'Copper','CL=F':'WTI Crude','BZ=F':'Brent Crude','NG=F':'Natural Gas',
  'NVDA':'NVIDIA','MSFT':'Microsoft','AMZN':'Amazon','GOOGL':'Alphabet','META':'Meta','AMD':'AMD','AVGO':'Broadcom',
  'TSM':'TSMC ADR','2330.TW':'TSMC','005930.KS':'Samsung','000660.KS':'SK Hynix',
  '8035.T':'Tokyo Electron','6857.T':'Advantest','9984.T':'SoftBank','BABA':'Alibaba','TCEHY':'Tencent',
};

// ── SESSION STORAGE CACHE ────────────────────────────────────────────
const CACHE = {
  set(k, v) { try { sessionStorage.setItem('mp_'+k, JSON.stringify({v, t:Date.now()})); } catch(e){} },
  get(k, maxAgeMs=86400000) {
    try {
      const raw = sessionStorage.getItem('mp_'+k);
      if (!raw) return null;
      const {v,t} = JSON.parse(raw);
      return (Date.now()-t < maxAgeMs) ? v : null;
    } catch(e){ return null; }
  }
};

// ── ROLLING DATA STORE (for z-score normalization) ───────────────────
const DS = {
  push(sym, pct) {
    if (pct == null || isNaN(pct)) return;
    const key = 'ds_'+sym;
    let arr = CACHE.get(key, 90*86400000) || [];
    arr.push(pct);
    if (arr.length > 30) arr = arr.slice(-30);
    CACHE.set(key, arr);
  },
  zScore(sym) {
    const arr = CACHE.get('ds_'+sym, 90*86400000) || [];
    if (arr.length < 3) return null;
    const mean = arr.reduce((a,b)=>a+b,0)/arr.length;
    const std  = Math.sqrt(arr.map(v=>(v-mean)**2).reduce((a,b)=>a+b,0)/arr.length);
    if (std===0) return 0;
    return (arr[arr.length-1]-mean)/std;
  },
  zToScore(z) {
    if (z==null) return null;
    return Math.round(((Math.max(-3,Math.min(3,z))+3)/6)*100);
  }
};

// ── GLOBAL STATE ─────────────────────────────────────────────────────
let GD = {};   // globalData: sym → {price, changePct, change, stale?}
let FX = {};   // fxData from Frankfurter: {EUR, GBP, JPY, INR}
let CD = {};   // cryptoData: {coins[], global{}}

// Quantitative state — single source of truth
const QS = {
  spxPct:null, ndxPct:null, djiPct:null, rutPct:null,
  yield3m:null, yield10y:null, yield30y:null,
  yield10yPct:null, yield3mPct:null,
  dxyPct:null, dxyPrice:null,
  goldPct:null, copperPct:null, oilPct:null, brentPct:null,
  nvdaPct:null, tsmPct:null, amdPct:null, msftPct:null,
  inrPct:null, inrPrice:null, niftyPct:null, niftyPrice:null, bniftyPct:null,
  btcPct:null, ethPct:null, btcDom:null,
  curveSpread:null,  // 10Y - 3M
  fg: { composite:null, label:'No Data', color:'var(--txt-3)',
        equityMomentum:null, volatilityRegime:null, usdLiquidity:null,
        yieldCurve:null, goldSafeHaven:null, cryptoRisk:null, attribution:'' },
  regime: { dominant:'UNKNOWN', label:'Awaiting Data', confidence:0,
            scores:{growth:0,inflation:0,liquidity:0,stress:0},
            assetImplication:'', historicalAnalog:'' }
};

// ================================================================
// FETCH LAYER
// Strategy per data type:
//   Yahoo Finance → corsproxy.io first, allorigins fallback, then cache
//   Crypto        → CoinGecko direct, Binance direct fallback, cache
//   FX            → Frankfurter direct, open.er-api fallback, cache
// ================================================================

async function fetchRaw(url, timeout=CFG.FETCH_TIMEOUT) {
  const ctrl  = new AbortController();
  const timer = setTimeout(()=>ctrl.abort(), timeout);
  try {
    const r = await fetch(url, { signal: ctrl.signal });
    clearTimeout(timer);
    if (!r.ok) throw new Error('HTTP '+r.status);
    return r;
  } catch(e) { clearTimeout(timer); throw e; }
}

// Parse Yahoo chart API response
function parseYahoo(json) {
  const meta = json?.chart?.result?.[0]?.meta;
  if (!meta) return null;
  const price = meta.regularMarketPrice ?? meta.chartPreviousClose;
  const prev  = meta.previousClose      ?? meta.chartPreviousClose;
  if (!price) return null;
  const change    = prev ? price - prev : 0;
  const changePct = prev ? (change/prev)*100 : 0;
  return { price, change, changePct };
}

async function fetchYahooSymbol(sym) {
  const endpoints = [
    `https://query2.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(sym)}?interval=1d&range=1d`,
    `https://query1.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(sym)}?interval=1d&range=1d`,
  ];

  // Two proxy services tried in random order
  const proxies = shuffle([
    url => `https://corsproxy.io/?${encodeURIComponent(url)}`,
    url => `https://api.allorigins.win/get?url=${encodeURIComponent(url)}`,
    url => `https://corsproxy.org/?${encodeURIComponent(url)}`,
    url => `https://thingproxy.freeboard.io/fetch/${url}`,
  ]);

  for (const ep of endpoints) {
    for (const mkProxy of proxies) {
      const proxied = mkProxy(ep);
      try {
        const r   = await fetchRaw(proxied, 7000);
        let   json;
        if (proxied.includes('allorigins')) {
          const w = await r.json();
          if (!w?.contents) continue;
          json = JSON.parse(w.contents);
        } else {
          json = await r.json();
        }
        const result = parseYahoo(json);
        if (result) { CACHE.set('y_'+sym, result); return result; }
      } catch(e) { continue; }
    }
  }

  // All proxies failed — return cache (stale data is better than nothing)
  const cached = CACHE.get('y_'+sym);
  return cached ? { ...cached, stale:true } : null;
}

async function fetchAllYahoo() {
  const all = [
    ...SYM.us, ...SYM.eu, ...SYM.asia, ...SYM.india,
    ...SYM.yield, ...SYM.fx,  ...SYM.comm,
    ...SYM.ai_us, ...SYM.ai_tw, ...SYM.ai_jp,
  ];
  const results = {};
  for (let i=0; i<all.length; i+=CFG.CHUNK_SIZE) {
    const chunk   = all.slice(i, i+CFG.CHUNK_SIZE);
    const settled = await Promise.allSettled(chunk.map(s=>fetchYahooSymbol(s)));
    chunk.forEach((sym,idx)=>{
      if (settled[idx].status==='fulfilled' && settled[idx].value) {
        results[sym] = settled[idx].value;
      }
    });
    if (i+CFG.CHUNK_SIZE < all.length) await sleep(CFG.CHUNK_DELAY);
  }
  return results;
}

// ── CRYPTO: CoinGecko → Binance fallback ────────────────────────────
async function fetchCrypto() {
  // Try CoinGecko directly — it has CORS enabled
  try {
    const [coins, global] = await Promise.all([
      fetchRaw('https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&ids=bitcoin,ethereum,solana&order=market_cap_desc&per_page=3&sparkline=false&price_change_percentage=24h').then(r=>r.json()),
      fetchRaw('https://api.coingecko.com/api/v3/global').then(r=>r.json()),
    ]);
    if (coins?.length) {
      CACHE.set('crypto_coins',  coins);
      CACHE.set('crypto_global', global?.data);
      return { coins, global: global?.data };
    }
  } catch(e) {}

  // Binance fallback (native CORS) — only gives BTC/ETH/SOL prices
  try {
    const tickers = await fetchRaw('https://api.binance.com/api/v3/ticker/24hr?symbols=["BTCUSDT","ETHUSDT","SOLUSDT"]').then(r=>r.json());
    const MAP = { BTCUSDT:'bitcoin', ETHUSDT:'ethereum', SOLUSDT:'solana' };
    const NAMES_B = { BTCUSDT:'Bitcoin', ETHUSDT:'Ethereum', SOLUSDT:'Solana' };
    const coins = tickers.map(t=>({
      id:   MAP[t.symbol],
      name: NAMES_B[t.symbol],
      current_price: parseFloat(t.lastPrice),
      price_change_percentage_24h: parseFloat(t.priceChangePercent),
      total_volume: parseFloat(t.volume)*parseFloat(t.lastPrice),
    }));
    CACHE.set('crypto_coins', coins);
    return { coins, global: CACHE.get('crypto_global') };
  } catch(e) {}

  // Return cache
  return {
    coins:  CACHE.get('crypto_coins')  || [],
    global: CACHE.get('crypto_global') || null,
  };
}

// ── FX: Frankfurter → open.er-api fallback ──────────────────────────
// Used to supplement Yahoo FX data and as primary source for
// currencies not in Yahoo (or when Yahoo proxies fail)
async function fetchFX() {
  try {
    const r = await fetchRaw('https://api.frankfurter.app/latest?from=USD&to=EUR,GBP,JPY,INR');
    const d = await r.json();
    if (d?.rates) {
      CACHE.set('fx_rates', d.rates);
      return d.rates;
    }
  } catch(e) {}

  try {
    const r = await fetchRaw('https://open.er-api.com/v6/latest/USD');
    const d = await r.json();
    if (d?.rates) {
      const rates = { EUR: d.rates.EUR, GBP: d.rates.GBP, JPY: d.rates.JPY, INR: d.rates.INR };
      CACHE.set('fx_rates', rates);
      return rates;
    }
  } catch(e) {}

  return CACHE.get('fx_rates') || {};
}

// ── NEWS: Reuters RSS → BBC Business fallback ────────────────────────
async function fetchNews() {
  const sources = [
    { url:'https://feeds.reuters.com/reuters/businessNews', name:'Reuters' },
    { url:'https://feeds.bbci.co.uk/news/business/rss.xml', name:'BBC Business' },
    { url:'https://rss.ft.com/rss/time/sections/us', name:'Financial Times' },
  ];
  const proxyUrl = u => `https://api.allorigins.win/get?url=${encodeURIComponent(u)}`;

  for (const src of sources) {
    try {
      const r    = await fetchRaw(proxyUrl(src.url), 8000);
      const wrap = await r.json();
      if (!wrap?.contents) continue;
      const doc   = new DOMParser().parseFromString(wrap.contents, 'text/xml');
      const items = Array.from(doc.querySelectorAll('item')).slice(0,10);
      if (!items.length) continue;
      const articles = items.map(el=>({
        title:       el.querySelector('title')?.textContent       || '',
        description: el.querySelector('description')?.textContent?.replace(/<[^>]+>/g,'') || '',
        pubDate:     el.querySelector('pubDate')?.textContent     || new Date().toISOString(),
        source:      src.name,
      }));
      CACHE.set('news', articles);
      return articles;
    } catch(e) { continue; }
  }
  return CACHE.get('news') || [];
}

// ── MACRO EVENTS: Econdb ─────────────────────────────────────────────
async function fetchEvents() {
  const today  = new Date().toISOString().slice(0,10);
  const future = new Date(Date.now()+45*86400000).toISOString().slice(0,10);
  const url    = `https://www.econdb.com/api/events/?date_from=${today}&date_to=${future}&format=json`;
  const HIGH   = ['cpi','ppi','nfp','payroll','fomc','gdp','pmi','interest rate','inflation','retail sales','ecb','rbi','boj','ism','core pce','unemployment'];
  const isHigh = n => { const l=n.toLowerCase(); return HIGH.some(k=>l.includes(k)); };

  try {
    const proxied = `https://api.allorigins.win/get?url=${encodeURIComponent(url)}`;
    const r   = await fetchRaw(proxied, 9000);
    const w   = await r.json();
    const d   = JSON.parse(w.contents);
    const res = (d?.results||d?.data||[]).filter(e=>isHigh(e.event||e.name||'')).slice(0,12);
    if (res.length) {
      const events = res.map(e=>({
        date:       (e.date||'').slice(0,10),
        name:       e.event||e.name||'—',
        country:    e.country||'—',
        prev:       e.previous!=null?String(e.previous):'—',
        forecast:   e.forecast!=null?String(e.forecast):'—',
        importance: e.importance===3?'h':e.importance===2?'m':'l',
      }));
      CACHE.set('events', events);
      return events;
    }
  } catch(e) {}
  return CACHE.get('events') || [];
}

// ================================================================
// POPULATE QUANTITATIVE STATE
// ================================================================
function populateQS() {
  const p  = sym => GD[sym]?.price      ?? null;
  const pc = sym => GD[sym]?.changePct  ?? null;

  QS.spxPct   = pc('^GSPC'); QS.ndxPct   = pc('^NDX');
  QS.djiPct   = pc('^DJI');  QS.rutPct   = pc('^RUT');
  QS.yield3m  = p('^IRX');   QS.yield3mPct = pc('^IRX');
  QS.yield10y = p('^TNX');   QS.yield10yPct = pc('^TNX');
  QS.yield30y = p('^TYX');
  QS.dxyPrice = p('DX-Y.NYB'); QS.dxyPct  = pc('DX-Y.NYB');
  QS.goldPct  = pc('GC=F');    QS.copperPct = pc('HG=F');
  QS.oilPct   = pc('CL=F');    QS.brentPct  = pc('BZ=F');
  QS.nvdaPct  = pc('NVDA');    QS.tsmPct   = pc('TSM');
  QS.amdPct   = pc('AMD');     QS.msftPct  = pc('MSFT');
  QS.inrPrice = p('USDINR=X'); QS.inrPct   = pc('USDINR=X');
  QS.niftyPrice= p('^NSEI');   QS.niftyPct = pc('^NSEI');
  QS.bniftyPct = pc('^NSEBANK');

  // Supplement FX from Frankfurter if Yahoo FX failed
  if (!QS.inrPrice && FX.INR) QS.inrPrice = FX.INR;

  const btc = (CD.coins||[]).find(c=>c.id==='bitcoin');
  const eth = (CD.coins||[]).find(c=>c.id==='ethereum');
  QS.btcPct = btc?.price_change_percentage_24h ?? null;
  QS.ethPct = eth?.price_change_percentage_24h ?? null;
  QS.btcDom = CD.global?.market_cap_percentage?.btc ?? null;

  if (QS.yield10y && QS.yield3m) QS.curveSpread = QS.yield10y - QS.yield3m;

  // Push to rolling store
  ['^GSPC','^NDX','^TNX','DX-Y.NYB','GC=F','HG=F','CL=F','NVDA','TSM'].forEach(s=>{
    if (GD[s]) DS.push(s, GD[s].changePct);
  });
}

// ================================================================
// FEAR & GREED ENGINE
// Weighted composite — 0=Extreme Fear, 100=Extreme Greed
// Only runs when ≥4 of 6 core inputs have real data
// ================================================================
function computeFearGreed() {
  const inputs  = [QS.spxPct, QS.ndxPct, QS.yield10yPct, QS.dxyPct, QS.goldPct, QS.btcPct];
  const loaded  = inputs.filter(v=>v!==null&&!isNaN(v)).length;

  if (loaded < 4) {
    QS.fg = { composite:null, label:'Awaiting Live Data', color:'var(--txt-3)', attribution:'' };
    return;
  }

  const sc = {};

  // 1. Equity Momentum (25%)
  const breadth = ['^GSPC','^NDX','^DJI','^RUT','^STOXX50E','^NSEI']
    .map(s=>GD[s]?.changePct).filter(v=>v!=null);
  const bScore  = breadth.length ? (breadth.filter(p=>p>0).length/breadth.length)*100 : 50;
  const spxZ    = DS.zScore('^GSPC');
  const zScore  = DS.zToScore(spxZ) ?? 50;
  const avgPct  = breadth.length ? breadth.reduce((a,b)=>a+b,0)/breadth.length : 0;
  const avgScore= Math.max(0,Math.min(100, 50+avgPct*25));
  sc.equityMomentum = 0.5*bScore + 0.3*zScore + 0.2*avgScore;

  // 2. Volatility Regime (20%) — invert: high vol = fear
  const yVol = Math.abs(QS.yield10yPct||0);
  const dVol = Math.abs(QS.dxyPct||0);
  const gVol = Math.abs(QS.goldPct||0);
  sc.volatilityRegime = 0.5*Math.max(0,Math.min(100,100-yVol*80))
                      + 0.3*Math.max(0,Math.min(100,100-dVol*60))
                      + 0.2*Math.max(0,Math.min(100,100-gVol*20));

  // 3. USD Liquidity (15%) — falling dollar = easing = greed
  const dxyZ = DS.zScore('DX-Y.NYB');
  const dxyS = dxyZ!=null ? DS.zToScore(-dxyZ) : Math.max(0,Math.min(100,50-(QS.dxyPct||0)*20));
  const eurPct = GD['EURUSD=X']?.changePct||0;
  sc.usdLiquidity = 0.7*(dxyS??50) + 0.3*Math.max(0,Math.min(100,50+eurPct*20));

  // 4. Yield Curve (15%)
  let curveScore = 50;
  if (QS.curveSpread!=null) {
    curveScore = Math.max(0,Math.min(100,((QS.curveSpread+1.5)/4.5)*100));
  }
  const velScore = (QS.yield10yPct!=null&&QS.yield3mPct!=null)
    ? Math.max(0,Math.min(100,50+(QS.yield10yPct-QS.yield3mPct)*15)) : 50;
  sc.yieldCurve = 0.7*curveScore + 0.3*velScore;

  // 5. Gold Safe Haven (10%)
  const gp=QS.goldPct||0, sp=QS.spxPct||0;
  let goldSafe;
  if (gp>0&&sp<0)      goldSafe = Math.max(0,  50-(Math.abs(gp)+Math.abs(sp))/2*15);
  else if (gp<0&&sp>0) goldSafe = Math.min(100, 50+(Math.abs(gp)+Math.abs(sp))/2*15);
  else                 goldSafe = Math.max(0,Math.min(100, 50-gp*8));
  const gcSpread = gp-(QS.copperPct||0);
  sc.goldSafeHaven = 0.6*goldSafe + 0.4*Math.max(0,Math.min(100,50-gcSpread*8));

  // 6. Crypto Risk (15%)
  const btcZ = DS.zToScore(DS.zScore('^GSPC')); // use SPX z as proxy if no BTC history
  const btcS = btcZ ?? Math.max(0,Math.min(100,50+(QS.btcPct||0)*5));
  const domS = QS.btcDom!=null ? (QS.btcDom>65?35:QS.btcDom>55?42:QS.btcDom>50?50:QS.btcDom>45?58:68) : 52;
  const relS = Math.max(0,Math.min(100,50-((QS.btcPct||0)-(QS.ethPct||0))*4));
  sc.cryptoRisk = 0.5*btcS + 0.3*domS + 0.2*relS;

  // Weighted composite
  const W = {equityMomentum:.25,volatilityRegime:.20,usdLiquidity:.15,yieldCurve:.15,goldSafeHaven:.10,cryptoRisk:.15};
  const composite = Math.round(Math.max(0,Math.min(100,
    Object.entries(W).reduce((acc,[k,w])=>acc+w*(sc[k]??50), 0)
  )));

  // Label
  const {label,color} = composite<=20 ? {label:'Extreme Fear',  color:'var(--red)'}
    : composite<=35 ? {label:'Fear',            color:'#ff7a35'}
    : composite<=50 ? {label:'Neutral-Fearful', color:'var(--gold)'}
    : composite<=65 ? {label:'Neutral-Greedy',  color:'#a8d8a8'}
    : composite<=80 ? {label:'Greed',           color:'#4ddd9a'}
    : {label:'Extreme Greed', color:'var(--green)'};

  // Attribution — which component deviated most from neutral (50)
  const topK = Object.entries(W).map(([k,w])=>({k,dev:w*Math.abs((sc[k]??50)-50)})).sort((a,b)=>b.dev-a.dev)[0]?.k;
  const lblMap = {equityMomentum:'equity breadth & momentum',volatilityRegime:'cross-asset volatility',usdLiquidity:'dollar liquidity',yieldCurve:'yield curve shape',goldSafeHaven:'gold/copper ratio',cryptoRisk:'crypto risk appetite'};
  const dir = (sc[topK]??50)>50?'greed':'fear';

  QS.fg = { ...sc, composite, label, color, attribution:`Driven by ${lblMap[topK]||topK} signalling ${dir}.` };
}

// ================================================================
// MACRO REGIME ENGINE — 4-Factor Model
// ================================================================
function computeRegime() {
  const inputs = [QS.spxPct, QS.yield10yPct, QS.dxyPct, QS.oilPct, QS.copperPct];
  if (inputs.filter(v=>v!=null).length < 3) {
    QS.regime = {dominant:'UNKNOWN',label:'Awaiting Data',confidence:0,scores:{growth:0,inflation:0,liquidity:0,stress:0},assetImplication:'',historicalAnalog:''};
    return;
  }

  const norm = (v,mn,mx) => v==null ? 0.5 : Math.max(0,Math.min(1,(v-mn)/(mx-mn)));
  const f = {};

  // Growth: equities up + copper up + curve positive + breadth
  const eq = ['^GSPC','^NDX','^DJI','^STOXX50E','^NSEI'].map(s=>GD[s]?.changePct??0);
  const breadth = eq.filter(p=>p>0).length/eq.length;
  f.growth = (breadth*.35 + norm(QS.copperPct,-1,2)*.25 + (QS.curveSpread>0?1:.2)*.25 + norm(QS.ndxPct,-1,2)*.15)*100;

  // Inflation: energy up + yield 3M rising + strong USD
  f.inflation = (norm(QS.oilPct,-1,3)*.30 + norm(QS.brentPct,-1,3)*.15 + norm(QS.goldPct,-.5,1.5)*.20 + ((QS.yield3mPct||0)>0?.8:.3)*.20 + ((QS.dxyPct||0)>.1?.7:.35)*.15)*100;

  // Liquidity: DXY falling + bonds rallying + equities + crypto up
  f.liquidity = (norm(-(QS.dxyPct||0),-.3,.3)*.30 + norm(-(QS.yield10yPct||0),-.2,.2)*.25 + norm(QS.spxPct||0,-.5,1.5)*.25 + norm(QS.btcPct||0,-2,5)*.20)*100;

  // Stress: gold up + equities down + yields spiking + USD surging + curve inverted
  const goldFlight = (QS.goldPct||0)>0 && (QS.spxPct||0)<0 ? Math.min(1,((QS.goldPct||0)-( QS.spxPct||0))/3) : .2;
  f.stress = (goldFlight*.25 + norm(-(QS.spxPct||0),-.5,2)*.25 + (Math.abs(QS.yield10yPct||0)>.3?.7:.3)*.15 + norm(QS.dxyPct||0,0,.8)*.20 + (QS.curveSpread!=null&&QS.curveSpread<0?.8:.3)*.15)*100;

  const sorted = Object.entries(f).sort((a,b)=>b[1]-a[1]);
  const [topKey, topVal] = sorted[0];
  const confidence = Math.max(25, Math.min(95, Math.round(topVal*.6+(topVal-sorted[1][1])*.8)));

  const META = {
    growth:    {label:'Cyclical Expansion',    assetImplication:'Long equities, copper, EM. Short bonds, defensives.', historicalAnalog:'Analogs: 2017 reflation, 2021 post-COVID reopening.'},
    inflation: {label:'Inflationary Pressure', assetImplication:'Long commodities, energy, TIPS. Underweight long-duration.',historicalAnalog:'Analogs: 2022 supply shock, 2008 pre-crisis commodity surge.'},
    liquidity: {label:'Liquidity Easing',      assetImplication:'Long growth equities, credit, crypto. Short USD.',      historicalAnalog:'Analogs: 2020 QE expansion, 2016 post-Brexit reflation.'},
    stress:    {label:'Risk Stress / Caution', assetImplication:'Long gold, short-end bonds. Raise cash, cut beta.',      historicalAnalog:'Analogs: 2020 COVID crash, 2018 Q4 liquidity crunch.'},
  };
  const m = META[topKey];
  QS.regime = { dominant:topKey.toUpperCase(), ...m, confidence, scores:f };
}

// ================================================================
// RENDER FUNCTIONS
// ================================================================

function renderClock() {
  const now = new Date();
  const el = $('headerTime');
  if (el) el.textContent = now.toUTCString().slice(17,25)+' UTC | '+now.toLocaleTimeString('en-IN',{timeZone:'Asia/Kolkata'})+' IST';
}

function detectSession() {
  const now = new Date();
  const utc = now.getUTCHours()*60 + now.getUTCMinutes();
  const day = now.getUTCDay();
  const wk  = day===0||day===6;
  const el  = $('sessionPill');
  if (!el) return;
  if (wk)                          { el.textContent='WEEKEND';          el.className='session-pill'; }
  else if (utc>=810&&utc<1200)     { el.textContent='🟢 US OPEN';       el.className='session-pill open'; }
  else if (utc>=630&&utc<810)      { el.textContent='🟡 US PRE-MKT';    el.className='session-pill'; }
  else if (utc>=420&&utc<930)      { el.textContent='🟡 EU OPEN';       el.className='session-pill open'; }
  else if (utc<420||utc>=1380)     { el.textContent='🔵 ASIA OPEN';     el.className='session-pill open'; }
  else                             { el.textContent='CLOSED';           el.className='session-pill'; }
}

function renderTicker() {
  const pairs = [
    ['tk-spx',  '^GSPC',      ''],
    ['tk-ndx',  '^NDX',       ''],
    ['tk-nifty','^NSEI',      ''],
    ['tk-gold', 'GC=F',       '$'],
    ['tk-oil',  'CL=F',       '$'],
    ['tk-dxy',  'DX-Y.NYB',   ''],
    ['tk-yield','^TNX',       '',  '%'],
    ['tk-nvda', 'NVDA',       '$'],
    ['tk-dax',  '^GDAXI',     ''],
    ['tk-nk',   '^N225',      ''],
    ['tk-hsi',  '^HSI',       ''],
  ];
  pairs.forEach(([id, sym, pre, suf]) => {
    const d = GD[sym]; if (!d) return;
    const pct = d.changePct||0;
    const col = pct>0?'var(--green)':pct<0?'var(--red)':'var(--txt-2)';
    const txt = (pre||'') + fmt(d.price,2) + (suf||'') + ' (' + fmtPct(pct) + ')';
    [`${id}`,`${id}2`].forEach(i=>{
      const el = $(i); if(el){ el.textContent=txt; el.style.color=col; }
    });
  });
  // BTC from CoinGecko
  const btc = (CD.coins||[]).find(c=>c.id==='bitcoin');
  if (btc) {
    const col = (btc.price_change_percentage_24h||0)>0?'var(--green)':'var(--red)';
    const txt = '$'+fmt(btc.current_price,0)+' ('+fmtPct(btc.price_change_percentage_24h)+')';
    ['tk-btc','tk-btc2'].forEach(i=>{const el=$(i);if(el){el.textContent=txt;el.style.color=col;}});
  }
}

function renderSignalBar() {
  const pairs = [
    ['sig-spx','sig-spx-ch','sig-spx-meta', '^GSPC', 'US Equities'],
    ['sig-ndx','sig-ndx-ch','sig-ndx-meta', '^NDX',  'Tech Index'],
  ];
  pairs.forEach(([idV,idC,idM,sym,meta])=>{
    const d=GD[sym]; if(!d) return;
    const el=$(idV); if(el) el.textContent=fmt(d.price);
    const ch=$(idC); if(ch){ ch.textContent=fmtPct(d.changePct); ch.className='sig-chg '+clr(d.changePct); }
    const m=$(idM); if(m) m.textContent=meta;
    const card=document.querySelector(`[data-sig="${sym}"]`);
    if(card) card.className='sig-card s-'+(d.changePct>0?'up':d.changePct<0?'down':'flat');
  });
  // Yield
  const tnx=GD['^TNX'];
  if(tnx){ $('sig-yield').textContent=tnx.price?tnx.price.toFixed(3)+'%':'—'; const c=$('sig-yield-ch'); if(c){c.textContent=fmtPct(tnx.changePct);c.className='sig-chg '+clr(tnx.changePct);}}
  // DXY
  const dxy=GD['DX-Y.NYB'];
  if(dxy){ $('sig-dxy').textContent=fmt(dxy.price,2); const c=$('sig-dxy-ch'); if(c){c.textContent=fmtPct(dxy.changePct);c.className='sig-chg '+clr(dxy.changePct);}}
  // BTC
  const btc=(CD.coins||[]).find(c=>c.id==='bitcoin');
  if(btc){ $('sig-btc').textContent='$'+fmt(btc.current_price,0); const c=$('sig-btc-ch'); if(c){c.textContent=fmtPct(btc.price_change_percentage_24h);c.className='sig-chg '+clr(btc.price_change_percentage_24h);}}
}

function renderHeatmap() {
  const syms = [...SYM.us.slice(0,2),...SYM.eu.slice(0,2),...SYM.asia.slice(0,2),'^NSEI','NVDA','GC=F','CL=F','HG=F'];
  const col = pct => pct>=2?'#006644':pct>=1?'#00875a':pct>=.3?'#2d5e44':pct>0?'#2d4d3a':pct<=-2?'#7a1a2e':pct<=-1?'#b91c2e':pct<=-.3?'#5e2030':'#3d2030';
  const el=$('heatmapGrid'); if(!el) return;
  el.innerHTML = syms.map(sym=>{
    const d=GD[sym]; const pct=d?.changePct||0;
    const tick=sym.replace(/\^|=X|=F|\.NS|\.T|\.TW|\.KS|\.HK/g,'').slice(0,6);
    return `<div class="hm-cell" style="background:${col(pct)}" title="${NAMES[sym]||sym}: ${fmtPct(pct)}"><div class="hm-name">${tick}</div><div class="hm-pct">${fmtPct(pct)}</div></div>`;
  }).join('');
}

function renderMarketRow(sym) {
  const d=GD[sym]; const pct=d?.changePct||0;
  const bar=Math.min(100,Math.abs(pct)*20);
  const stale = d?.stale ? ' <span style="font-size:9px;color:var(--gold)">CACHED</span>':''
  return `<div class="mkt-row" title="${NAMES[sym]||sym}">
    <div><div class="mkt-name">${NAMES[sym]||sym}${stale}</div><div class="mkt-tick">${sym}</div></div>
    <div class="mkt-price ${clr(pct)}">${d?fmt(d.price,2):'—'}</div>
    <div class="mkt-chg ${clr(pct)}">${fmtPct(pct)}</div>
    <div class="mkt-bar"><div class="mkt-bar-fill ${fillClr(pct)}" style="width:${bar}%"></div></div>
  </div>`;
}

function renderMarketsAll() {
  const regions = [
    {id:'us-markets',    syms:SYM.us,    statusId:'us-status'},
    {id:'eu-markets',    syms:SYM.eu,    statusId:'eu-status'},
    {id:'asia-markets',  syms:SYM.asia,  statusId:'asia-status'},
    {id:'india-markets', syms:SYM.india, statusId:'india-status'},
  ];
  const now=new Date(), utc=now.getUTCHours()*60+now.getUTCMinutes(), day=now.getUTCDay(), wk=day===0||day===6;
  const isOpen = {
    'us-status':   !wk&&utc>=810&&utc<1200,
    'eu-status':   !wk&&utc>=420&&utc<930,
    'asia-status': !wk&&(utc<420||utc>=1380),
    'india-status':!wk&&utc>=330&&utc<600,
  };
  regions.forEach(r=>{
    const el=$(r.id); if(el) el.innerHTML=r.syms.map(renderMarketRow).join('');
    const st=$(r.statusId); if(st){
      if(wk){st.textContent='WEEKEND';st.className='mkt-status s-closed';}
      else if(isOpen[r.statusId]){st.textContent='OPEN';st.className='mkt-status s-open';}
      else{st.textContent='CLOSED';st.className='mkt-status s-closed';}
    }
  });
}

function renderAITracker() {
  const panels=[
    {id:'ai-us',  syms:SYM.ai_us, hdr:'🇺🇸 US Megacaps'},
    {id:'ai-tw',  syms:SYM.ai_tw, hdr:'🇹🇼 TW / KR'},
    {id:'ai-rest',syms:SYM.ai_jp, hdr:'🇯🇵 JP / CN'},
  ];
  panels.forEach(p=>{
    const hdrEl=document.querySelector(`[data-ai-hdr="${p.id}"]`);
    if(hdrEl) hdrEl.textContent=p.hdr;
    const rows=p.syms.map(sym=>{
      const d=GD[sym]; const pct=d?.changePct||0;
      const badge=pct>=2?'<span class="badge b-lead">LEAD</span>':pct<=-2?'<span class="badge b-lag">LAG</span>':Math.abs(pct)>=3?'<span class="badge b-odd">ODD</span>':'';
      const tick=sym.replace(/\.NS|\.T|\.TW|\.KS|\.HK/g,'');
      return {pct, html:`<div class="ai-row"><span class="ai-ticker">${tick}</span><span class="ai-name">${NAMES[sym]||sym}</span>${badge}<span class="ai-price">${d?fmt(d.price,2):'—'}</span><span class="ai-chg ${clr(pct)}">${fmtPct(pct)}</span></div>`};
    }).sort((a,b)=>b.pct-a.pct);
    const el=$(p.id); if(el) el.innerHTML=rows.map(r=>r.html).join('');
  });
}

function renderCommodities() {
  const comms=[
    {sym:'GC=F', name:'Gold',        icon:'🥇', unit:'/oz',   sig:pct=>pct>.5?'Safe-haven buying — risk-off signal':pct<-.5?'Gold weak — risk appetite returning':'Stable — no flight to safety'},
    {sym:'SI=F', name:'Silver',      icon:'⚪', unit:'/oz',   sig:pct=>pct>1?'Industrial + safe-haven demand surge':'Subdued'},
    {sym:'HG=F', name:'Copper',      icon:'🟤', unit:'/lb',   sig:pct=>pct>.5?'▲ Growth signal — industrial demand rising':pct<-.5?'▼ Demand concern — growth slowing':'Neutral'},
    {sym:'CL=F', name:'WTI Crude',   icon:'🛢️', unit:'/bbl',  sig:pct=>pct>1?'Inflation pressure rising':pct<-1?'Demand weakness / deflationary':'Balanced supply-demand'},
    {sym:'BZ=F', name:'Brent Crude', icon:'⛽', unit:'/bbl',  sig:pct=>pct>0?'Global tightening':'Supply ample'},
    {sym:'NG=F', name:'Natural Gas', icon:'🔥', unit:'/MMBtu',sig:pct=>pct>2?'Energy spike — supply cut or demand surge':'Gas prices subdued'},
  ];
  const el=$('commodityGrid'); if(!el) return;
  el.innerHTML=comms.map(c=>{
    const d=GD[c.sym]; const pct=d?.changePct||0;
    return `<div class="comm-card"><div class="comm-icon">${c.icon}</div><div class="comm-name">${c.name}</div><div class="comm-price">${d?fmt(d.price,2):'—'}</div><div class="comm-chg ${clr(pct)}">${fmtPct(pct)} <span style="font-size:10px;color:var(--txt-3);font-weight:400;">${c.unit}</span></div><div class="comm-sig">${c.sig(pct)}</div></div>`;
  }).join('');
}

function renderYields() {
  const ys=[
    {sym:'^IRX',label:'3-Month T-Bill', sub:'Fed funds proxy'},
    {sym:'^FVX',label:'5-Year Note',    sub:'Medium-term'},
    {sym:'^TNX',label:'10-Year Note',   sub:'Benchmark rate'},
    {sym:'^TYX',label:'30-Year Bond',   sub:'Long-term'},
  ];
  const el=$('yieldsTable'); if(!el) return;
  el.innerHTML=ys.map(y=>{
    const d=GD[y.sym]; const pct=d?.changePct||0;
    const gauge=Math.min(100,(d?.price||0)/8*100);
    return `<div class="rate-row"><div><div class="rate-name">${y.label}</div><div class="rate-sub">${y.sub}</div></div><div class="rate-bar"><div class="rate-bar-fill" style="width:${gauge}%"></div></div><div class="rate-val">${d?d.price.toFixed(3)+'%':'—'}</div><div class="rate-chg ${clr(pct)}">${fmtPct(pct)}</div></div>`;
  }).join('');

  // Yield curve chart
  const vals=['^IRX','^FVX','^TNX','^TYX'].map(s=>GD[s]?.price??null);
  drawYieldCurve(['3M','5Y','10Y','30Y'],vals);

  // Curve spread annotation
  if(QS.curveSpread!=null){
    const el=$('curveSpreadLbl');
    if(el){ const bps=Math.round(QS.curveSpread*100); el.textContent=`10Y–3M Spread: ${bps>0?'+':''}${bps}bps ${bps<0?'⚠ INVERTED':'✓'}`; el.style.color=bps<0?'var(--red)':bps>100?'var(--green)':'var(--gold)'; }
  }
}

function renderFX() {
  const pairs=[
    {sym:'EURUSD=X',label:'EUR/USD',sub:'Euro'},
    {sym:'GBPUSD=X',label:'GBP/USD',sub:'Cable'},
    {sym:'USDJPY=X',label:'USD/JPY',sub:'Yen'},
    {sym:'DX-Y.NYB',label:'DXY Index',sub:'Dollar Index'},
    {sym:'USDINR=X', label:'USD/INR',sub:'Rupee'},
  ];
  const el=$('fxTable'); if(!el) return;
  el.innerHTML=pairs.map(f=>{
    const d=GD[f.sym]; const pct=d?.changePct||0;
    // Supplement with Frankfurter if Yahoo failed
    let price=d?.price;
    if(!price&&FX){
      if(f.sym==='EURUSD=X'&&FX.EUR) price=FX.EUR;
      if(f.sym==='GBPUSD=X'&&FX.GBP) price=FX.GBP;
      if(f.sym==='USDJPY=X'&&FX.JPY) price=FX.JPY;
      if(f.sym==='USDINR=X'&&FX.INR) price=FX.INR;
    }
    const gauge=Math.min(100,Math.abs(pct)*30+30);
    return `<div class="rate-row"><div><div class="rate-name">${f.label}</div><div class="rate-sub">${f.sub}</div></div><div class="rate-bar"><div class="rate-bar-fill" style="width:${gauge}%"></div></div><div class="rate-val">${price?fmt(price,4):'—'}</div><div class="rate-chg ${clr(pct)}">${fmtPct(pct)}</div></div>`;
  }).join('');
}

function renderCrypto() {
  const btc=(CD.coins||[]).find(c=>c.id==='bitcoin');
  const eth=(CD.coins||[]).find(c=>c.id==='ethereum');
  const sol=(CD.coins||[]).find(c=>c.id==='solana');
  const g=CD.global;

  const set=(pid,cid,vid,coin)=>{
    if(!coin) return;
    const p=$(pid); if(p) p.textContent='$'+fmt(coin.current_price,2);
    const c=$(cid); if(c){c.textContent=fmtPct(coin.price_change_percentage_24h);c.className='c-chg '+clr(coin.price_change_percentage_24h);}
    const v=$(vid); if(v) v.textContent='Vol: $'+(coin.total_volume/1e9).toFixed(2)+'B';
  };
  set('btc-price','btc-chg','btc-vol',btc);
  set('eth-price','eth-chg','eth-vol',eth);
  set('sol-price','sol-chg','sol-vol',sol);

  const dom=g?.market_cap_percentage?.btc;
  if(dom){
    const el=$('btc-dom'); if(el) el.textContent=dom.toFixed(1)+'%';
    const sig=$('dom-signal');
    if(sig){ sig.textContent=dom>65?'BTC dominance very high — defensive crypto':dom>55?'Balanced':'Altcoin season — max risk appetite'; sig.className='c-chg '+(dom>55?'flat':'up'); }
  }
  const mc=g?.total_market_cap?.usd;
  const el=$('total-mcap'); if(el&&mc) el.textContent='MCap: $'+(mc/1e12).toFixed(2)+'T';
}

function renderFearGreed() {
  const fg=QS.fg;
  const s=$('gaugeScore'); if(s){s.textContent=fg.composite??'N/A';s.style.color=fg.color;}
  const l=$('gaugeLabel'); if(l){l.textContent=(fg.label).toUpperCase();l.style.color=fg.color;}
  const n=$('gaugeNeedle'); if(n) n.style.left=(fg.composite??50)+'%';

  const comps=[
    ['gc-eq','gcb-eq',  fg.equityMomentum],
    ['gc-vol','gcb-vol',fg.volatilityRegime],
    ['gc-usd','gcb-usd',fg.usdLiquidity],
    ['gc-crv','gcb-crv',fg.yieldCurve],
    ['gc-gld','gcb-gld',fg.goldSafeHaven],
    ['gc-cry','gcb-cry',fg.cryptoRisk],
  ];
  const gc=v=>v<=30?'var(--red)':v<=45?'#ff7a35':v<=55?'var(--gold)':v<=70?'#4ddd9a':'var(--green)';
  comps.forEach(([vi,bi,val])=>{
    const v=Math.round(val??50);
    const ve=$(vi); if(ve){ve.textContent=fg.composite!==null?v:'—';ve.style.color=gc(v);}
    const be=$(bi); if(be){be.style.width=(fg.composite!==null?v:0)+'%';be.style.background=gc(v);}
  });
}

function renderRegime() {
  const r=QS.regime;
  const el=$('regimeItems'); if(!el) return;
  const CLS={growth:'active-growth',inflation:'active-inflation',liquidity:'active-liquidity',stress:'active-stress'};
  el.innerHTML=Object.keys(CLS).map(k=>{
    const score=Math.round(r.scores?.[k]||0);
    const active=k===r.dominant.toLowerCase();
    return `<div class="regime-item ${active?CLS[k]:''}" title="${k}: ${score}/100">${k.charAt(0).toUpperCase()+k.slice(1)}${active?` <span style="font-size:9px;opacity:.7">(${r.confidence}%)</span>`:''}</div>`;
  }).join('');
  const c=$('regimeConf'); if(c) c.textContent=`${r.label} — ${r.confidence}% confidence`;
  const f=$('confFill'); if(f) f.style.width=r.confidence+'%';
}

function renderSummary(got) {
  const fg=QS.fg, r=QS.regime, el=$('summaryText');
  if(!el) return;
  if(!got||fg.composite===null){
    el.innerHTML=`<strong>MacroPulse</strong> — <strong style="color:var(--red)">No live data loaded.</strong> Proxies may be rate-limited. Auto-retrying every 45s. If this persists, hard-refresh the page (Ctrl+Shift+R). Curated by <strong>Yuvraj Sureka</strong>.`;
    return;
  }
  const q=got>30?'Full':got>15?'Partial':'Limited';
  el.innerHTML=`<strong>MacroPulse</strong> — ${q} data (${got} instruments). Fear &amp; Greed: <strong style="color:${fg.color}">${fg.label} (${fg.composite}/100)</strong>. ${fg.attribution} Regime: <strong>${r.label}</strong>. ${r.assetImplication} Curated by <strong>Yuvraj Sureka</strong>.`;
}

function renderNews(articles) {
  const CATS=[
    {cat:'nc-fed',   label:'CENTRAL BANK',keys:['fed','fomc','powell','rate cut','rate hike','federal reserve','ecb','rbi','boe','boj','central bank','monetary policy']},
    {cat:'nc-ai',    label:'AI / TECH',   keys:['nvidia','ai','artificial intelligence','semiconductor','chip','tsmc','openai','amd','microsoft','google']},
    {cat:'nc-macro', label:'MACRO',       keys:['cpi','inflation','gdp','jobs','nfp','pmi','ism','recession','retail sales','ppi']},
    {cat:'nc-geo',   label:'GEO',         keys:['china','russia','ukraine','war','sanction','tariff','trade','nato','iran','opec']},
    {cat:'nc-energy',label:'ENERGY',      keys:['oil','crude','brent','wti','opec','natural gas','energy','petroleum']},
  ];
  const classify = t => { const tl=t.toLowerCase(); for(const c of CATS) if(c.keys.some(k=>tl.includes(k))) return c; return {cat:'nc-macro',label:'MARKETS'}; };
  const sentiment= t => { const tl=t.toLowerCase(); const b=['surge','rally','rise','gain','beat','strong','record','cut rate'].filter(w=>tl.includes(w)).length; const r=['fall','drop','crash','decline','miss','weak','recession','war','tighten'].filter(w=>tl.includes(w)).length; return b>r?'bullish':r>b?'bearish':'neutral'; };
  const ago = d => { const m=(Date.now()-new Date(d).getTime())/60000; return m<60?Math.round(m)+'m ago':m<1440?Math.round(m/60)+'h ago':Math.round(m/1440)+'d ago'; };

  const el=$('newsGrid'); if(!el) return;
  if(!articles||!articles.length){
    el.innerHTML=`<div class="news-item" style="grid-column:1/-1;text-align:center;padding:24px;color:var(--txt-3);font-family:var(--f-mono);font-size:11px;">News feed unavailable — RSS proxy blocked. Try a hard refresh.</div>`;
    $('newsTimestamp').textContent='—';
    return;
  }
  el.innerHTML=articles.slice(0,6).map(a=>{
    const cat=classify(a.title);
    const imp=sentiment(a.title);
    const desc=(a.description||'').slice(0,130);
    return `<div class="news-item"><div class="news-hdr"><span class="news-cat ${cat.cat}">${cat.label}</span><span class="news-time">${ago(a.pubDate)}</span></div><div class="news-hl">${a.title}</div><div class="news-imp ${imp}">→ ${desc}${desc.length>=130?'...':''}</div><div class="news-src">${a.source}</div></div>`;
  }).join('');
  $('newsTimestamp').textContent='Updated '+new Date().toLocaleTimeString();
}

function renderEvents(events) {
  const el=$('eventsList'); if(!el) return;
  if(!events||!events.length){
    el.innerHTML=`<div style="padding:18px;text-align:center;font-size:11px;color:var(--txt-3);font-family:var(--f-mono);">Calendar data unavailable — Econdb proxy failed. Retrying next cycle.</div>`;
    return;
  }
  el.innerHTML=events.map(e=>`<div class="event-row"><div class="ev-imp imp-${e.importance}"></div><div class="ev-date">${e.date}</div><div class="ev-name">${e.name}</div><div class="ev-ctry">${e.country}</div><div><div class="ev-lbl">Prev</div><div class="ev-prev">${e.prev}</div></div><div><div class="ev-lbl">Fcst</div><div class="ev-fore">${e.forecast}</div></div></div>`).join('');
}

function renderIndiaPanel() {
  const nifty =GD['^NSEI'];
  const bnifty=GD['^NSEBANK'];
  const inr   =GD['USDINR=X'];
  const rel   =GD['RELIANCE.NS'];
  const tcs   =GD['TCS.NS'];

  const set=(vid,sub,d,inv=false)=>{
    const v=$(vid); const s=$(sub);
    if(!d){if(v)v.textContent='N/A';return;}
    const p=d.changePct||0;
    if(v){v.textContent=fmt(d.price,2);v.style.color=(inv?-p:p)>0?'var(--green)':'var(--red)';}
    if(s){s.textContent=fmtPct(p)+' today';s.className='ind-sub '+clr(inv?-p:p);}
  };
  set('ind-nifty', 'ind-nifty-sub',  nifty);
  set('ind-bnifty','ind-bnifty-sub', bnifty);
  set('ind-inr',   'ind-inr-sub',    inr,   true); // invert: rising USD/INR = INR weak
  set('ind-rel',   'ind-rel-sub',    rel);
  set('ind-tcs',   'ind-tcs-sub',    tcs);

  // Computed signal
  const sig=$('indiaSignalText'); if(!sig) return;
  const msgs=[];
  if(nifty)  msgs.push(`Nifty ${fmtPct(nifty.changePct)} ${(nifty.changePct||0)>1?'— strong domestic bid.':(nifty.changePct||0)<-1?'— selling pressure.':'— rangebound.'}`);
  if(bnifty&&nifty){ const sp=(bnifty.changePct||0)-(nifty.changePct||0); msgs.push(sp>.5?'Banks outperforming — rate-cut optimism.':sp<-.5?'Banks lagging — NIM concerns.':'Broad market aligned with banks.'); }
  if(inr){ const p=inr.changePct||0; msgs.push(p>.3?'INR under pressure — watch RBI intervention.':p<-.3?'INR strengthening — FII inflows or USD softness.':'INR stable.'); }
  if(QS.dxyPct!=null&&QS.dxyPct<-.2) msgs.push('Weak USD supportive for INR and EM inflows.');
  if(QS.goldPct!=null&&QS.goldPct>.5&&QS.spxPct!=null&&QS.spxPct<0) msgs.push('Global risk-off — monitor FII outflow risk.');
  sig.textContent=msgs.length?msgs.join(' '):'All India indicators within normal range.';
}

// World Bank for India structural data (non-blocking)
async function fetchIndiaFundamentals() {
  async function wb(indicator) {
    const url=`https://api.worldbank.org/v2/country/IN/indicator/${indicator}?format=json&mrv=1&per_page=1`;
    try { const r=await fetchRaw(url,6000); const d=await r.json(); const v=d?.[1]?.[0]; if(v?.value!=null) return {value:v.value,year:v.date}; } catch(e){}
    try {
      const p=`https://api.allorigins.win/get?url=${encodeURIComponent(url)}`;
      const r=await fetchRaw(p,6000); const w=await r.json(); const d=JSON.parse(w.contents); const v=d?.[1]?.[0]; if(v?.value!=null) return {value:v.value,year:v.date};
    } catch(e){}
    return null;
  }
  const [cpi,rate]=await Promise.allSettled([wb('FP.CPI.TOTL.ZG'),wb('FR.INR.LEND')]);
  const cpiData =cpi.status==='fulfilled' ?cpi.value :null;
  const rateData=rate.status==='fulfilled'?rate.value:null;
  if(cpiData){
    const el=$('ind-cpi-val'); if(el){el.textContent=cpiData.value.toFixed(1)+'%';el.style.color=cpiData.value>6?'var(--red)':cpiData.value>4?'var(--gold)':'var(--green)';}
    const sub=$('ind-cpi-sub'); if(sub) sub.textContent=`CPI YoY — World Bank ${cpiData.year}`;
  }
  if(rateData){
    const el=$('ind-rate-val'); if(el){el.textContent=rateData.value.toFixed(2)+'%';el.style.color='var(--blue)';}
    const sub=$('ind-rate-sub'); if(sub) sub.textContent=`Lending rate — World Bank ${rateData.year}`;
  }
}

function renderCrossAssetSignals() {
  const inputs=[QS.spxPct,QS.yield10yPct,QS.dxyPct];
  const el=$('signalsGrid'); if(!el) return;
  if(inputs.filter(v=>v!=null).length<2){
    el.innerHTML=`<div class="signal-card"><div class="sig-icon">📡</div><div class="sig-content"><span class="sig-type type-watch">NO DATA</span><div class="sig-heading">Signal engine requires live data</div><div class="sig-desc">Host on GitHub Pages or Netlify to enable live cross-asset signals.</div></div></div>`;
    return;
  }
  const sigs=[];
  const fmtV=v=>v!=null?fmtPct(v):'—';

  // Equity vs Yield
  if(QS.spxPct!=null&&QS.yield10yPct!=null){
    const se=QS.spxPct>.3,ed=QS.spxPct<-.3,yu=QS.yield10yPct>.05,yd=QS.yield10yPct<-.05;
    if(se&&yd) sigs.push({icon:'💧',type:'type-bullish',label:'LIQUIDITY RALLY',h:`SPX ${fmtV(QS.spxPct)} + Yields ${fmtV(QS.yield10yPct)}`,d:`Equities up while yields fall signals liquidity-driven rally, not growth. Bond market pricing lower-for-longer, boosting equity multiples. ${QS.curveSpread!=null?`10Y–3M spread: ${Math.round(QS.curveSpread*100)}bps.`:''} Watch DXY for dollar liquidity confirmation.`});
    else if(se&&yu) sigs.push({icon:'⚡',type:'type-watch',label:'GROWTH RALLY',h:`SPX ${fmtV(QS.spxPct)} + Yields ${fmtV(QS.yield10yPct)}`,d:'Co-movement of equities and yields signals growth optimism, not just liquidity. Markets pricing stronger nominal GDP. Cyclical sectors and value over growth in this regime.'});
    else if(ed&&yu) sigs.push({icon:'🔴',type:'type-bearish',label:'STAGFLATION SIGNAL',h:`SPX ${fmtV(QS.spxPct)} + Yields ${fmtV(QS.yield10yPct)}`,d:'Equities falling while yields rise is the worst combo for multi-asset portfolios. Inflation forcing yields up while growth deteriorates. Reduce duration and equity beta simultaneously.'});
    else if(ed&&yd) sigs.push({icon:'🛡️',type:'type-caution',label:'FLIGHT TO QUALITY',h:`SPX ${fmtV(QS.spxPct)} + Bonds rallying`,d:'Classic risk-off. Treasuries functioning as equity hedge. Duration likely to outperform. Watch credit spreads for severity assessment.'});
  }

  // Yield curve
  if(QS.curveSpread!=null){
    const bps=Math.round(QS.curveSpread*100);
    if(QS.curveSpread<-.25) sigs.push({icon:'⚠️',type:'type-bearish',label:'CURVE INVERTED',h:`10Y–3M: ${bps}bps INVERTED`,d:`The 10Y–3M spread is the Fed's preferred recession indicator (Estrella-Mishkin). At ${bps}bps inversion, historical recession probability within 12 months is elevated. Bank NIMs compressed — watch credit conditions.`});
    else if(QS.curveSpread>1.5) sigs.push({icon:'📈',type:'type-bullish',label:'STEEP CURVE',h:`10Y–3M: +${bps}bps`,d:'Steep positive curve signals growth expectations without immediate rate hike pressure. Bank profitability improves. Historically early-cycle expansion signal.'});
  }

  // Dollar liquidity
  if(QS.dxyPct!=null){
    if(QS.dxyPct>.3&&QS.spxPct!=null&&QS.spxPct<0) sigs.push({icon:'💵',type:'type-bearish',label:'USD TIGHTENING',h:`DXY ${fmtV(QS.dxyPct)} — Dollar Stress`,d:'Strong dollar + equity weakness signals global dollar liquidity tightening. EM currencies under pressure. Mechanically tightens financial conditions globally without Fed action.'});
    else if(QS.dxyPct<-.3&&QS.spxPct!=null&&QS.spxPct>.3) sigs.push({icon:'🌊',type:'type-bullish',label:'DOLLAR EASING',h:`DXY ${fmtV(QS.dxyPct)} — Liquidity Released`,d:'Weaker dollar easing global financial conditions — passive stimulus for EM economies. Capital rotating into EM equities and commodities. INR should benefit; watch FII flows into India.'});
  }

  // Commodities
  if(QS.oilPct!=null&&QS.copperPct!=null){
    if(QS.oilPct>1&&QS.copperPct>1) sigs.push({icon:'🏭',type:'type-watch',label:'COMMODITY SURGE',h:`Oil ${fmtV(QS.oilPct)} + Copper ${fmtV(QS.copperPct)}`,d:'Energy and industrial metals rising together signals genuine global demand expansion. Positive for commodity exporters. Inflationary for import-dependent economies like India and Japan.'});
    else if(QS.oilPct>1.5&&QS.copperPct<-.5) sigs.push({icon:'🛢️',type:'type-bearish',label:'SUPPLY SHOCK OIL',h:`Oil ${fmtV(QS.oilPct)} surging, Copper ${fmtV(QS.copperPct)}`,d:'Oil supply disruption pattern (not demand-driven). Inflates CPI while copper weakness signals soft industrial demand. Stagflation risk. Central banks face policy dilemma.'});
  }

  // AI semis
  if(QS.nvdaPct!=null&&QS.tsmPct!=null){
    const avg=(QS.nvdaPct+QS.tsmPct+(QS.amdPct||0))/3;
    const z=DS.zScore('NVDA');
    if(z!=null&&Math.abs(z)>1.5) sigs.push({icon:'🧠',type:z>0?'type-bullish':'type-bearish',label:z>0?'AI CAPEX SURGE':'SEMI CONCERN',h:`NVDA ${fmtV(QS.nvdaPct)} | TSM ${fmtV(QS.tsmPct)} | AMD ${fmtV(QS.amdPct)}`,d:z>0?`Semiconductor complex at ${Math.abs(z).toFixed(1)}σ above recent average — statistically significant AI capex momentum. NVDA/TSM co-movement confirms demand-driven, not NVDA-specific.`:`Semiconductor complex at ${Math.abs(z).toFixed(1)}σ below average — potential inventory correction or demand pull-forward. Watch NVDA data center guidance and TSMC utilization.`});
    else if(avg>1.5) sigs.push({icon:'🧠',type:'type-bullish',label:'AI FLOW +',h:`Semi breadth: NVDA ${fmtV(QS.nvdaPct)}, TSM ${fmtV(QS.tsmPct)}`,d:'Semiconductor sector breadth positive across US and Taiwan — supply chain confirmation of AI infrastructure spending. Both NVDA (demand) and TSM (capacity) rising = capex cycle intact.'});
  }

  if(!sigs.length){
    el.innerHTML=`<div class="signal-card"><div class="sig-icon">🔎</div><div class="sig-content"><span class="sig-type type-watch">MONITORING</span><div class="sig-heading">No significant cross-asset divergences detected</div><div class="sig-desc">All major relationships within normal ranges. Regime: ${QS.regime.label}. Monitor for directional signal.</div></div></div>`;
    return;
  }
  el.innerHTML=sigs.map(s=>`<div class="signal-card"><div class="sig-icon">${s.icon}</div><div class="sig-content"><span class="sig-type ${s.type}">${s.label}</span><div class="sig-heading">${s.h}</div><div class="sig-desc">${s.d}</div></div></div>`).join('');
}

// ── YIELD CURVE CHART ────────────────────────────────────────────────
let yChart=null;
function drawYieldCurve(labels,vals){
  const ctx=$('yieldCurveChart'); if(!ctx) return;
  const valid=vals.map(v=>v??null);
  const normal=valid[3]&&valid[0]&&valid[3]>valid[0];
  const color=normal?'#00e5a0':'#ff4d6a';
  if(yChart){ yChart.data.datasets[0].data=valid; yChart.data.datasets[0].borderColor=color; yChart.data.datasets[0].backgroundColor=color+'22'; yChart.update('none'); }
  else {
    yChart=new Chart(ctx,{type:'line',data:{labels,datasets:[{label:'Yield Curve',data:valid,borderColor:color,backgroundColor:color+'22',borderWidth:2,pointRadius:4,pointBackgroundColor:color,fill:true,tension:.3}]},options:{responsive:true,maintainAspectRatio:false,animation:{duration:300},plugins:{legend:{display:false}},scales:{x:{grid:{color:'rgba(255,255,255,.04)'},ticks:{color:'#555568',font:{family:'Space Mono',size:10}}},y:{grid:{color:'rgba(255,255,255,.04)'},ticks:{color:'#555568',font:{family:'Space Mono',size:10},callback:v=>v?.toFixed(2)+'%'}}}}});
  }
}

// ── COUNTDOWN TIMER ──────────────────────────────────────────────────
let countdownInt=null;
function startCountdown(){
  let n=45;
  const el=$('nextRefresh');
  if(countdownInt) clearInterval(countdownInt);
  countdownInt=setInterval(()=>{
    n--;
    if(el) el.textContent='Next: '+n+'s';
    if(n<=0) clearInterval(countdownInt);
  },1000);
}

// ================================================================
// MAIN REFRESH CYCLE
// ================================================================
async function refreshAll(){
  const btn=$('refreshBtn'); if(btn) btn.classList.add('loading');
  const sumEl=$('summaryText');
  if(sumEl) sumEl.innerHTML='<strong>MacroPulse</strong> — Fetching live data... first load takes 20–30 seconds.';

  try {
    // All fetches run in parallel where possible
    const [yahooData, cryptoData, fxData] = await Promise.all([
      fetchAllYahoo(),
      fetchCrypto(),
      fetchFX(),
    ]);

    GD = yahooData;
    CD = cryptoData;
    FX = fxData;

    const got=Object.keys(GD).length;

    // Quant engine
    populateQS();
    computeFearGreed();
    computeRegime();

    // Render everything
    renderSignalBar();
    renderTicker();
    renderHeatmap();
    renderMarketsAll();
    renderAITracker();
    renderCommodities();
    renderYields();
    renderFX();
    renderCrypto();
    renderFearGreed();
    renderRegime();
    renderCrossAssetSignals();
    renderIndiaPanel();
    renderSummary(got);

    // Flash
    document.querySelectorAll('.sig-card').forEach(el=>{el.classList.remove('flash');void el.offsetWidth;el.classList.add('flash');});

    // Status
    const stale=Object.values(GD).filter(d=>d?.stale).length;
    const fresh=got-stale;
    $('lastRefresh').textContent=`Refreshed: ${new Date().toLocaleTimeString()} — ${fresh} live${stale?', '+stale+' cached':''}`;

    startCountdown();

    // Background fetches (non-blocking)
    fetchNews().then(renderNews).catch(()=>renderNews([]));
    fetchEvents().then(renderEvents).catch(()=>renderEvents([]));
    fetchIndiaFundamentals().catch(()=>{});

  } catch(e) {
    console.error('Refresh error:',e);
    renderSummary(Object.keys(GD).length);
    startCountdown();
  } finally {
    if(btn) btn.classList.remove('loading');
  }
}

// ================================================================
// INIT
// ================================================================
function init(){
  renderClock();
  setInterval(renderClock, 1000);
  setInterval(detectSession, 30000);
  detectSession();
  refreshAll();
  setInterval(refreshAll, CFG.REFRESH_MS);
}

document.addEventListener('DOMContentLoaded', init);
