// ==UserScript==
// @name         B站成分查询
// @namespace    bilibili.chengfen.online
// @version      1.2.1
// @author       Huizs
// @license      GPL-3.0
// @icon         https://static.hdslb.com/images/favicon.ico
// @description  评论区楼层自动挂成分标签；直播间弹幕栏用户名旁挂同一个查询按钮；点击楼层图标打开单人面板：首屏并发 card 与动态首页，勋章墙 / 关注列表 / 动态翻页在后台补全。规则（增删改 / 导入导出 / 恢复默认，内置更新按 id 合并）。
// @match        https://*.bilibili.com/*
// @connect      api.bilibili.com
// @connect      api.live.bilibili.com
// @connect      api.aicu.cc
// @connect      seibun.moe
// @connect      relay-drh.pages.dev
// @require      https://cdn.jsdelivr.net/npm/js-md5@0.8.3/src/md5.js
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @run-at       document-end
// @updateURL    https://raw.githubusercontent.com/Huizs/bilibili-chengfen-query/main/bilibili-chengfen-query.js
// @downloadURL  https://raw.githubusercontent.com/Huizs/bilibili-chengfen-query/main/bilibili-chengfen-query.js
// @supportURL   https://github.com/Huizs/bilibili-chengfen-query/issues
// ==/UserScript==


/* md5 用 @require 而不是内联：内联就得带未压缩源码（+19 KB），本站不收压缩代码。
 * 钉死 0.8.3 的 src/md5.js；取不到时 getSigned 直接返回失败，不会静默退成默认标签。 */

(function () {
    'use strict';

    /* 目录（按代码顺序）
     *  1 配置 · 2 工具 · 3 WBI 签名 · 4 HTTP 三队列+风控退避 · 5 缓存工厂与六只桶
     *  6 官方数据源 card/videos/动态（裸请求优先，-352 才验签兜底）· 7 成分规则表与用户可编辑层
     *  8 命中归因 PATH_LABELS/collectCorpus/evidence/analyze · 9 状态与分桶 · 10 标签页加载动作
     * 11 渲染（五个标签页 + STYLE）· 12 面板事件与拖拽 · 13 楼层图标/自动标签/Shadow 穿透/直播间
     * 14 启动三触发
     */

    /* ══════════════ 配置 ══════════════ */

    const CFG = {
        biliGap: 120, biliJitter: 80, biliCooldownMs: 6000,        // B站官方接口：仅抑制同一瞬间的并发聚集
        seibunGap: 300, seibunJitter: 120, seibunCooldownMs: 10000, // seibun 为普通站点接口，无需按 B站 WAF 的标准保守处理
        aicuGap: 700, aicuJitter: 400, aicuCooldownMs: 15000,      // aicu 的 468 滑块已实测触发，保持严格
        retryDelay: [1200, 2000],
        // -429 为 aicu 的软限流：HTTP 200 但响应体 code=-429，仅按状态码判断会漏
        riskCodes: new Set([-352, -412, -429]),
        aicuTimeout: 8000,             // 超时即判定不可达，避免点击后长时间无响应

        ps: 20,                        // 两个源统一 20 条/页：控制响应体大小，并使分页有意义
        seiLimit: 20,
        dmPs: 100,                     // 弹幕单页 100 条：每页需两个请求（取号 + 查询），页数不宜过多
        cacheTtl: 3600 * 1000,         // 响应缓存 1 小时
        cacheMaxEntries: 100,
        floorTtl: 30 * 60 * 1000,      // 楼层自动标签：一个人 30 分钟内不重复查（存 GM，刷新不清）
        floorMaxEntries: 300,
        personTtl: 10 * 60 * 1000,     // 面板按人缓存：10 分钟（纯内存，刷新即清）

        // ── 四个上限均为天花板而非配额：正常路径不会触及 ──
        dynPages: 3,                   // 面板里一个人最多翻 3 页动态（楼层仍然只 1 页）
        floorInflight: 20,             // 楼层自动标签同时在飞的上限；首屏 20 人正好一轮全发
        floorMargin: 800,              // 楼层视口裁剪：上下各 800px 内才查，屏幕外不发
        floorContainersMax: 600,       // 已挂标签楼层的记账上限，超出时剔除已销毁的那些

        // ── 播放器弹幕列表反查 ──
        dmSegMs: 360000,               // B站 弹幕分段实测 6 分钟（view 的 segment_size=360000）
        dmSegCacheMax: 12,             // 已解析分段的只数上限：段内含弹幕正文，只在内存
        dmSegEntriesMax: 6000,         // 单段保留的弹幕条数上限（B站 服务端本身就有截断）
        dmUidTtl: 30 * 24 * 3600e3,    // midHash→UID 是稳定映射，给 30 天只为兜住算法变更
        dmUidMax: 800,
    };

    /* ══════════════ 工具 ══════════════ */

    const sleep = ms => new Promise(r => setTimeout(r, ms));
    const esc = s => String(s ?? '').replace(/[&<>"']/g,
        m => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[m]));
    const num = v => (v == null || v === '' ? '—' : typeof v === 'number' ? v.toLocaleString('zh-CN') : String(v));
    const fmtTs = ts => ts ? new Date(ts * 1000).toLocaleString('zh-CN', { hour12: false }) : '—';
    const clamp = (v, min, max) => Math.min(Math.max(v, min), Math.max(min, max));

    /* ══════════════ WBI 签名（签名串与发送串必须逐字节一致，否则 -352） ══════════════ */

    const MIXIN_TAB = [46,47,18,2,53,8,23,32,15,50,10,31,58,3,45,35,27,43,5,49,33,9,42,19,29,28,14,39,12,38,41,13,37,48,7,16,24,55,40,61,26,17,0,1,60,51,30,4,22,25,54,21,56,59,6,63,57,62,11,36,20,34,44,52];
    const mixinKey = (img, sub) => { let s = ''; for (const i of MIXIN_TAB) s += (img + sub)[i] ?? ''; return s.slice(0, 32); };
    const qsEncode = str => encodeURIComponent(String(str))
        .replace(/%20/g, '+')
        .replace(/[!'()]/g, c => '%' + c.charCodeAt(0).toString(16).toUpperCase().padStart(2, '0'))
        .replace(/\*/g, '%2A');

    function encWbi(params, img, sub) {
        const t = Object.keys(params).reduce((a, k) => { a[k] = String(params[k]).replace(/[!'()*]/g, ''); return a; }, {});
        t.wts = Math.round(Date.now() / 1000);
        const query = Object.keys(t).sort().map(k => `${qsEncode(k)}=${qsEncode(t[k])}`).join('&');
        t.w_rid = md5(query + mixinKey(img, sub));
        // 发送串必须与签名串完全一致，否则 -352
        return Object.keys(t).sort().map(k => `${qsEncode(k)}=${qsEncode(t[k])}`).join('&');
    }

    /* ══════════════ HTTP：三条队列 + 风控重试 ══════════════
     * bili = B站官方：生效的是 WBI 签名与 cookie，节奏只抑制同一瞬间的并发聚集；
     */
    const lanes = {
        bili: { chain: Promise.resolve(), until: 0, gap: CFG.biliGap, jitter: CFG.biliJitter, cooldown: CFG.biliCooldownMs },
        seibun: { chain: Promise.resolve(), until: 0, gap: CFG.seibunGap, jitter: CFG.seibunJitter, cooldown: CFG.seibunCooldownMs },
        aicu: { chain: Promise.resolve(), until: 0, gap: CFG.aicuGap, jitter: CFG.aicuJitter, cooldown: CFG.aicuCooldownMs },
    };

    function xhr(opts) {
        return new Promise(resolve => GM_xmlhttpRequest({
            ...opts,
            onload: res => resolve({ status: res.status, text: opts.responseType ? '' : res.responseText, buf: res.response }),
            // net 表示连接层失败（DNS、断网、连接被重置）。与风控的区别在于：只要返回了任意 HTTP 状态码即视为网络可达，468 亦然。
            onerror: () => resolve({ net: true, fail: '连不上（DNS/断网/连接被重置）' }),
            ontimeout: () => resolve({ net: true, fail: '连接超时' }),
        }));
    }

    async function send(method, url, { timeout, referer, body, binary } = {}) {
        const headers = {};
        if (referer) { headers.referer = referer; headers['x-referer'] = referer; }
        if (body) headers['content-type'] = 'application/json';
        // 无额外请求头时不传 headers 字段，与 aicu 的可用调用形态保持一致
        const r = await xhr({ method, url, timeout: timeout || 10000, headers: Object.keys(headers).length ? headers : undefined, data: body,
            responseType: binary ? 'arraybuffer' : undefined, anonymous: false });
        if (r.fail) return r;
        if (r.status === 412 || r.status === 429 || r.status === 468) return { risk: true, fail: `HTTP ${r.status}`, text: r.text };
        // 弹幕分段越界时 B站 回 304 空体，这是"这一段没弹幕"而不是失败
        if (binary) return (r.status === 200 || r.status === 304) ? { bin: r.buf || new ArrayBuffer(0) } : { fail: `HTTP ${r.status}` };
        if (r.status !== 200) return { fail: `HTTP ${r.status}`, text: r.text };
        let json;
        try { json = JSON.parse(r.text); }
        catch (e) { return { fail: '响应非 JSON（WAF 验证页/滑块页）', html: (r.text || '').slice(0, 120) }; }
        if (CFG.riskCodes.has(json.code)) return { risk: true, json, fail: `code=${json.code}` };
        return { json };
    }

    function enqueue(lane, task) {
        const L = lanes[lane];
        L.chain = L.chain.then(async () => {
            await sleep(Math.max(0, L.until - Date.now()) + L.gap + Math.random() * L.jitter);
            try { return await task(); } catch (e) { return { fail: String(e) }; }
        });
        return L.chain;
    }

    async function paced(method, url, opts = {}, lane = 'bili') {
        const L = lanes[lane];
        return enqueue(lane, async () => {
            let last = { fail: '未发起请求' };
            for (let i = 0; i < CFG.retryDelay.length; i++) {
                last = await send(method, url, opts);
                if (!last.risk && !last.net) return last;
                await sleep(CFG.retryDelay[i] + Math.random() * 600);
            }
            // 仅风控才冷却泳道；连接失败说明未到达服务端，冷却无意义，直接把原因返回给调用方
            if (last.risk) L.until = Date.now() + L.cooldown;
            return { fail: last.fail || '风控拦截', net: !!last.net };
        });
    }

    const get = (url, opts = {}, lane = 'bili') => paced('GET', url, opts, lane);
    // aicu 的排队取号为 POST 且不带 body
    const post = (url, opts = {}, lane = 'aicu') => paced('POST', url, opts, lane);

    // 免签名的公开接口（card）：不入队、不预置延迟，仅在风控或连接失败时退避重试一次
    async function getNow(url, opts = {}) {
        let r = await send('GET', url, opts);
        if (r.net || r.risk) {
            await sleep(600 + Math.random() * 400);
            r = await send('GET', url, opts);
        }
        return r.risk || r.net ? { fail: r.fail || '风控拦截', net: !!r.net } : r;
    }

    async function getSigned(url, params, opts = {}, lane = 'bili') {
        if (typeof md5 !== 'function') return { fail: 'md5 库未加载（@require 未取到）' };
        const keys = await wbiKeys();
        if (!keys) return { fail: 'WBI 密钥获取失败' };
        return get(`${url}?${encWbi(params, keys.img, keys.sub)}`, opts, lane);
    }

    let keysCache = null, keysAt = 0;
    async function wbiKeys() {
        if (keysCache && Date.now() - keysAt < 10 * 60 * 1000) return keysCache;
        const r = await send('GET', 'https://api.bilibili.com/x/web-interface/nav', { timeout: 8000 });
        const wbi = r.json?.data?.wbi_img;
        if (!wbi) return null;
        keysCache = { img: wbi.img_url.split('/').pop().split('.')[0], sub: wbi.sub_url.split('/').pop().split('.')[0] };
        keysAt = Date.now();
        return keysCache;
    }

    /* ══════════════ 缓存：一个工厂 + 六只桶 ══════════════
     * gmKey 决定落 GM 存储还是只留内存；TTL 与条数上限统一，内存版按插入序 LRU。
     *   indexCache  索引页响应 1h 落 GM · dmCache 弹幕正文 1h 仅内存 · tagCache 楼层标签 30min 落 GM
     *   personCache 单人 card+动态原文 10min 仅内存 · buckets 每人每源末页 仅内存 · domProfile 楼层 DOM 资料
     */
    /* GM 版的读写成本：整份对象常驻内存镜像，读不再每次反序列化；
     * 写只标脏，200ms 合并落盘一次（首屏 20 人不再触发 20 次全量序列化）。
     * 落盘时以磁盘为底、只覆盖本实例改过的键，多标签页同时开不互相丢数据。 */
    function mkCache({ gmKey = null, ttl = Infinity, max = 100 } = {}) {
        const mem = gmKey ? null : new Map();
        const alive = e => e && Date.now() - e.ts < ttl;
        let mirror = null, timer = null;
        const touched = new Set();
        const load = () => (mirror = mirror || GM_getValue(gmKey, {}) || {});
        const flush = () => {
            timer = null;
            if (!touched.size) return;
            const disk = GM_getValue(gmKey, {}) || {};
            touched.forEach(k => { disk[k] = mirror[k]; });
            touched.clear();
            const ks = Object.keys(disk);
            if (ks.length > max) ks.slice(0, ks.length - max).forEach(x => delete disk[x]);
            GM_setValue(gmKey, disk);
        };
        if (gmKey) addEventListener('pagehide', flush);   // 关页前把未落盘的写入补上
        return {
            get(k) {
                const key = String(k), e = gmKey ? load()[key] : mem.get(key);
                if (!alive(e)) return null;
                if (mem) { mem.delete(key); mem.set(key, e); }
                return e.v;
            },
            set(k, v) {
                const key = String(k), e = { v, ts: Date.now() };
                if (!gmKey) {
                    mem.delete(key); mem.set(key, e);
                    while (mem.size > max) mem.delete(mem.keys().next().value);
                    return;
                }
                load()[key] = e;
                touched.add(key);
                if (!timer) timer = setTimeout(flush, 200);
            },
            patch(k, p) { this.set(k, { ...(this.get(k) || {}), ...p }); },
            clear() {
                if (!gmKey) return mem.clear();
                mirror = {}; touched.clear(); flush();
                GM_setValue(gmKey, {});
            },
        };
    }

    const indexCache = mkCache({ gmKey: 'cfq_index_cache', ttl: CFG.cacheTtl, max: CFG.cacheMaxEntries });
    // 弹幕正文不写入 GM 存储：仅存内存一小时，刷新即清
    const dmCache = mkCache({ ttl: CFG.cacheTtl, max: 80 });
    const tagCache = mkCache({ gmKey: 'cfq_floor_cache_v2', ttl: CFG.floorTtl, max: CFG.floorMaxEntries });
    const personCache = mkCache({ ttl: CFG.personTtl, max: 80 });
    // 播放器弹幕列表：分段里含弹幕正文，只进内存；midHash→UID 不含正文，才落 GM
    const dmSegCache = mkCache({ ttl: CFG.cacheTtl, max: CFG.dmSegCacheMax });
    const dmUidCache = mkCache({ gmKey: 'cfq_dm_uid', ttl: CFG.dmUidTtl, max: CFG.dmUidMax });
    const domProfile = mkCache({ max: 300 });

    const qsBuild = params => Object.entries(params)
        .filter(([, v]) => v !== undefined && v !== null && v !== '')
        .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(String(v))}`).join('&');

    /* ── 对外地址全部集中在这一处 ──
     * 更换域名、增减线路、调整地址形式都只改这里；调用点只引用 API_PATH 的名字。
     * 直连 = 各站原域名；加速源 = 同一个中转站下加一段前缀，路径原样拼在后面（两边路径完全一致）。 */
    const EP = {
        relay:  'https://relay-drh.pages.dev',
        aicu:   { direct: 'https://api.aicu.cc',  via: 'aicu' },
        seibun: { direct: 'https://seibun.moe',   via: 'seibun' },
    };
    const API_PATH = {
        reply:    '/api/v3/search/getreply',        // 评论页 aicu 源
        enqueue:  '/api/v4/queue/enqueue',          // 弹幕取号
        dmSearch: '/api/v4/search/',                // + getvideodm / getlivedm
        comments: '/api/comments',                  // 评论页 seibun 源
        resolve:  '/api/bilibili/resolve-user',     // 用户名 → UID
    };
    // 唯一决定「本次走直连还是走加速源」的位置
    const via = (name, path) => state.relay ? `${EP.relay}/${EP[name].via}${path}` : `${EP[name].direct}${path}`;
    // 缓存 key 必须包含线路，否则切换数据源后仍命中旧缓存，表现为开关未生效
    const lineTag = () => state.relay ? 'r1' : 'r0';
    // 面板灰字文案：两个评论索引源与弹幕源均不在境内，三处共用这一句
    const AICU_NOTE = '国内网络环境可能无法使用';

    /**
     * 两个评论索引源，均无需排队取票：
     *   aicu   —— v3 接口，参数与历史版本一致；
     *   seibun—— B站二游评论查询站，/api/comments 直接给 bvid、服务端 cursor 翻页。
     * cands = [{key, url, parse}]，按顺序试到成功为止。
     */
    async function indexSearch(cands) {
        for (const c of cands) {
            const hit = indexCache.get(c.key);
            if (hit) return { ...hit, cached: true, src: c.name };
        }
        const errs = [];
        for (const c of cands) {
            const r = await get(c.url, c.opts || {}, c.lane);
            const parsed = r.json ? c.parse(r.json) : null;
            if (parsed) {
                const out = { data: parsed, fail: null, src: c.name };
                indexCache.set(c.key, out);
                return out;
            }
            const why = r.fail || (r.json?.error?.message ? r.json.error.message : (r.json ? `code=${r.json.code}` : '无响应'));
            errs.push(`${c.name} → ${why}`);
        }
        return { fail: errs.join('；') };
    }

     /* aicu v4（弹幕接口仅 v4 有）。实测：
      *   取号 POST /api/v4/queue/enqueue → {ticket,status,position}，当前恒为 ready/0；
      *   每张票只能用一次，重复用返回 -419，故单页需两个请求、翻页也要重新取号；
      *   触发惩罚的是未消费的票：只取号不查询，第 3 张起返回 -429（HTTP 仍 200）。
     */
    // path 例：'getvideodm' / 'getlivedm'
    async function aicuV4(path, params) {
        const o = { timeout: CFG.aicuTimeout };
        const e = await post(via('aicu', API_PATH.enqueue), o);
        if (e.fail) return { fail: `取号失败：${e.fail}` };
        const d = e.json?.data;
        if (e.json?.code !== 0 || !d?.ticket) return { fail: `取号失败 code=${e.json?.code} ${e.json?.message || ''}`.trim() };
        // 排队依赖 SSE 事件且跨域不可达，因此存在排队时本次直接放弃，不阻塞等待
        if (d.status !== 'ready') return { fail: `aicu 排队中（前面约 ${d.position} 人），本次放弃` };
        const r = await get(`${via('aicu', API_PATH.dmSearch)}${path}?${qsBuild({ ...params, ticket: d.ticket })}`, o, 'aicu');
        if (r.fail) return { fail: `查询失败：${r.fail}` };
        if (r.json?.code === -403) return { fail: `aicu 关了这个接口：${r.json.message || ''}` };
        if (r.json?.code !== 0) return { fail: `查询失败 code=${r.json?.code} ${r.json?.message || ''}`.trim() };
        return { json: r.json };
    }

    /* ══════════════ B站官方侧数据源（「查询」标签页） ══════════════ */

    const space = (mid, tail = '') => `https://space.bilibili.com/${mid}/${tail}`;

    const API = {
        // card 免签名且为首屏唯一必需请求，因此不入任何队列
        async card(mid) { return (await getNow(`https://api.bilibili.com/x/web-interface/card?mid=${mid}`)).json?.data || null; },
        /* 粉丝勋章墙：免签名、单次、不分页。medal_name 精确匹配优先于关键词推断，level 作强度。
         * close_space_medal=1 是「隐藏了勋章墙」，与「无勋章」含义不同，需分开上报。 */
        async medals(mid) {
            const r = await getNow(`https://api.live.bilibili.com/xlive/web-ucenter/user/MedalWall?target_id=${mid}`, { referer: space(mid) });
            if (r.fail) return { fail: r.fail };
            const d = r.json?.code === 0 ? r.json.data : null;
            if (!d) return { fail: `code=${r.json?.code}` };
            return {
                closed: !!d.close_space_medal,
                list: (d.list || []).map(x => ({
                    name: x.medal_info?.medal_name || '', level: Number(x.medal_info?.level) || 0,
                    mid: String(x.medal_info?.target_id || ''), target: x.medal_info?.target_name || '',
                })),
            };
        },
        /* 关注列表：免签名可访问，但多数账号设了隐私（code 22115），且每页仅 20 条，故最多翻 3 页。 */
        async follows(mid, pages = 3) {
            const out = [];
            for (let pn = 1; pn <= pages; pn++) {
                const r = await get(`https://api.bilibili.com/x/relation/followings?vmid=${mid}&pn=${pn}&ps=20`, { referer: space(mid) });
                const j = r.json;
                if (j?.code === 22115) return { hidden: true, list: out };
                if (j?.code !== 0) return { fail: r.fail || `code=${j?.code}`, list: out };
                const list = j.data?.list || [];
                out.push(...list.map(x => ({ mid: String(x.mid || ''), name: x.uname || '', sign: x.sign || '', off: x.official_verify?.desc || '', type: x.official_verify?.type })));
                if (list.length < 20) return { list: out, end: true };
            }
            return { list: out, truncated: true };
        },
        // 以下三个接口仅用于 生日 / 精确获赞 / 总播放量 三格，首屏不等待（见 fetchExtra）
        async accInfo(mid) {
            const r = await getSigned('https://api.bilibili.com/x/space/wbi/acc/info', { mid }, { referer: space(mid) });
            return r.json?.code === 0 ? r.json.data : { __fail: r.fail || `code=${r.json?.code}` };
        },
        async relation(mid) {
            const r = await getSigned('https://api.bilibili.com/x/relation/stat', { vmid: mid }, { referer: space(mid) });
            return r.json?.code === 0 ? r.json.data : { __fail: r.fail || `code=${r.json?.code}` };
        },
        async upstat(mid) {
            const r = await getSigned('https://api.bilibili.com/x/space/upstat', { mid }, { referer: space(mid) });
            return r.json?.code === 0 ? r.json.data : { __fail: r.fail || `code=${r.json?.code}` };
        },
        async videos(mid) {
            const r = await getSigned('https://api.bilibili.com/x/space/wbi/arc/search',
                { mid, ps: 50, tid: 0, pn: 1, keyword: '', order: 'pubdate', platform: 'web', web_location: 1550101, order_avoided: 'true' },
                { referer: space(mid, 'video'), timeout: 15000 });
            if (r.json?.code !== 0) return { list: [], total: 0, fail: r.fail || `code=${r.json?.code}` };
            return { list: r.json.data?.list?.vlist || [], total: r.json.data?.page?.count ?? 0, fail: null };
        },
    };

    /* 验签版单页动态，仅在裸请求被 -352 拦截后兜底。参数名 host_mid（host_uid 返回 4101129）。 */
    async function dynSigned(uid) {
        const r = await getSigned('https://api.bilibili.com/x/polymer/web-dynamic/v1/feed/space',
            { offset: '', host_mid: String(uid), timezone_offset: '-480', features: 'itemOpusList' },
            { referer: space(uid) });
        return r.json?.code === 0 && r.json.data ? { data: r.json.data } : { fail: r.fail || `code=${r.json?.code}` };
    }

    /* ══════════════ 成分规则表 ══════════════
     * 内置条目衍生自 bilibili_auto_labeling（MIT，© 2026 TPPPP，https://github.com/TPPPP72/bilibili_auto_labeling），
     * 显示名与多数关键词沿用其表，新增词/勋章名/关注名与「崩坏系列」等为本次扩展。
     * 字段：id 稳定标识（改名改词与删除记账都靠它）· g 分组 · n 显示名 · k 匹配词（| 或 & 与 @games 任一作品名）
     *       c 颜色 · m 期望粉丝牌名 · o 关注列表匹配名
     * 显示名用作品名/粉丝牌名，组名进悬浮提示。匹配词只增不减；不保留裸「碧蓝」（航线/档案/幻想/之海四向重叠无主导）。
     */
    const DEFAULT_RULES = [
        // ── V圈：显示名即粉丝牌名本身，替换为主播名会丢失信息，保持原样 ──
        { id: 'fan_jia',      g: 'V圈', n: '嘉心糖', k: '嘉心糖|嘉然',        c: '#E799B0', m: '嘉心糖', o: '嘉然' },
        { id: 'fan_tafei',    g: 'V圈', n: '雏草姬', k: '雏草姬|塔菲',        c: '#FF00CC', m: '雏草姬', o: '塔菲' },
        { id: 'fan_dongxl',   g: 'V圈', n: '棺材板', k: '棺材板|東雪蓮',      c: '#C0C0C0', m: '棺材板', o: '東雪蓮' },
        { id: 'fan_qihai',    g: 'V圈', n: '杰尼',   k: '杰尼|七海',          c: '#947583', m: '杰尼',   o: '七海' },
        { id: 'fan_maolei',   g: 'V圈', n: '喵喵露', k: '喵喵露|猫雷',        c: '#00FF00', m: '喵喵露', o: '猫雷' },
        { id: 'fan_xgoushuo', g: 'V圈', n: '三畜',   k: '三畜|小狗说',        c: '#B8A6D9', m: '三畜',   o: '小狗说' },
        { id: 'fan_xiangwan', g: 'V圈', n: '顶碗人', k: '顶碗人|向晚',        c: '#9AC8E2', m: '顶碗人', o: '向晚' },
        { id: 'fan_beila',    g: 'V圈', n: '贝极星', k: '贝极星|贝拉',        c: '#DB7D74', m: '贝极星', o: '贝拉' },
        { id: 'fan_nailin',   g: 'V圈', n: '奶淇琳', k: '奶淇琳|乃琳',        c: '#576690', m: '奶淇琳', o: '乃琳' },
        { id: 'fan_xingtong', g: 'V圈', n: '小星星', k: '小星星|星瞳',        c: '#E0E0E0', m: '小星星', o: '星瞳' },
        { id: 'fan_zi',       g: 'V圈', n: '小孩梓', k: '小孩梓|梓',          c: '#9900FF', m: '小孩梓', o: '梓' },
        { id: 'fan_miku',     g: 'V圈', n: '骑士团', k: '初音|miku|MIKU',     c: '#00CC99', m: '骑士团', o: '初音' },
        { id: 'fan_lty',      g: 'V圈', n: '洛天依', k: '天依',               c: '#33CCFF', m: '',       o: '洛天依' },

        // ── 二游 ──
        { id: 'g2_huanta',    g: '二游', n: '幻塔',           k: '幻塔', c: '#FFCC66' },
        { id: 'g2_zhanshuang',g: '二游', n: '战双帕弥什',     k: '战双|帕弥什', c: 'pink' },
        { id: 'g2_mingchao',  g: '二游', n: '鸣潮',           k: '鸣潮|库洛|漂泊者', c: 'pink' },
        { id: 'g2_zzz',       g: '二游', n: '绝区零',         k: '绝区零|邦布|Zenless Zone Zero', c: '#0066FF' },
        { id: 'g2_bh3',       g: '二游', n: '崩坏3',          k: '崩坏3|崩坏三|崩三|崩坏学院|3rd', c: '#0066FF' },
        { id: 'g2_starrail',  g: '二游', n: '崩坏：星穹铁道', k: '星穹铁道|崩铁|星铁|帕姆', c: '#0066FF' },
        { id: 'g2_bhxz2',     g: '二游', n: '崩坏学园2',      k: '崩坏学园2|崩2|崩学2', c: '#0066FF' },
        { id: 'g2_guangyu',   g: '二游', n: '光遇',           k: '光遇', c: 'pink' },
        { id: 'g2_azurlane',  g: '二游', n: '碧蓝航线',       k: '碧蓝航线|蛮啾', c: '#33CCC' },
        { id: 'g2_bluearch',  g: '二游', n: '蔚蓝档案',       k: '蔚蓝档案|碧蓝档案|基沃托斯|阿拜多斯', c: '#33CCC' },
        { id: 'g2_fgo',       g: '二游', n: '冠位指定',       k: 'FGO|fgo|冠位指定|命运-冠位指定|Fate', c: 'pink' },
        { id: 'g2_priconne',  g: '二游', n: '公主连结',       k: '公主连结|超得', c: '#CCFF99' },
        { id: 'g2_touhou',    g: '二游', n: '东方Project',    k: '东方project|东方Project|灵梦|博丽灵梦|芙兰朵露|魔理沙|八云紫|幻想乡|ZUN', c: 'pink' },
        { id: 'g2_yuanshen',  g: '二游', n: '原神',           k: '原神|genshin|提瓦特|蒙德|璃月', c: '#6600CC' },
        { id: 'g2_arknights', g: '二游', n: '明日方舟',       k: '明日方舟|罗德岛|鹰角|阿米娅|干员', c: '#6600CC' },
        { id: 'g2_wzry',      g: '二游', n: '王者荣耀',       k: '王者荣耀|王者农药|KPL|kpl', c: '#6600CC' },
        { id: 'g2_endfield',  g: '二游', n: '终末地',         k: '终末地|Endfield', c: '#6600CC' },
        { id: 'g2_yihuan',    g: '二游', n: '异环',           k: '异环|NTE|Neverness To Everness', c: 'pink' },
        { id: 'g2_wuxianda',  g: '二游', n: '无限大',         k: '代号无限大|无限大|Ananta|Project Ananta', c: 'pink' },

        // ── 网游 ──
        { id: 'g3_xianjian',  g: '网游', n: '仙剑',     k: '仙剑', c: '#6666FF' },
        { id: 'g3_gujian',    g: '网游', n: '古剑',     k: '古剑', c: '#6666FF' },
        { id: 'g3_nishuihan', g: '网游', n: '逆水寒',   k: '逆水寒', c: '#6666FF' },
        { id: 'g3_zhuxian',   g: '网游', n: '诛仙世界', k: '诛仙世界', c: '#6666FF' },
        { id: 'g3_jw3',       g: '网游', n: '剑网3',    k: '剑网3|剑网|指尖江湖|缘起', c: '#6666FF' },

        // ── 端游 ──
        { id: 'g4_hsh',    g: '端游', n: '黑神话：悟空', k: '黑神话|天命人|黑马喽', c: '#6699FF' },
        { id: 'g4_lol',    g: '端游', n: '英雄联盟',     k: '英雄联盟|LOL|LPL|lpl|Faker|拳头', c: '#6699FF' },
        { id: 'g4_cod',    g: '端游', n: '使命召唤',     k: '使命召唤|COD|cod|战区', c: '#6699FF' },
        { id: 'g4_val',    g: '端游', n: '无畏契约',     k: '无畏契约|瓦罗兰特|VALORANT|源能行动', c: '#6699FF' },
        { id: 'g4_naraka', g: '端游', n: '永劫无间',     k: '永劫无间|NARAKA|naraka', c: '#6699FF' },

        // ── 主机 ──
        { id: 'g5_zelda', g: '主机', n: '塞尔达传说', k: '塞尔达|旷野之息|王国之泪|Zelda|zelda|海拉鲁', c: '#FF6699' },
        { id: 'g5_mh',    g: '主机', n: '怪物猎人',   k: '怪物猎人|怪猎', c: '#FF6699' },

        // ── 混沌 ──
        { id: 'g6_mc',    g: '混沌', n: '我的世界',   k: 'MINECRAFT|Minecraft|我的世界', c: '#006600' },
        { id: 'g6_ut',    g: '混沌', n: '传说之下',   k: 'UNDERTALE|undertale|Undertale|传说之下', c: '#333366' },
        { id: 'g6_scp',   g: '混沌', n: 'SCP基金会',  k: 'SCP', c: '#330000' },

        // ── 弱证据：抽奖转发。裸「抽奖」会把「转发抽手机」一并计入，因此要求同现一个作品名 ──
        { id: 'g7_lottery', g: '', n: '动态抽奖', k: '抽奖&@games', c: '#254680' },
    ];

    // 无命中时的默认标签
    const DEFAULT_TAG = { name: '【 普通 |  纯良】', color: '#11DD77' };
    // 接口失败时的标签：与「无命中」区分，避免把查询失败呈现为无成分
    const ERROR_TAG = { name: '【 查询失败/无动态 】', color: '#999999' };

    // 仅为 6 位 hex 追加透明度后缀，避免 "pink80" 这类非法值使边框失效
    const withAlpha = c => /^#[0-9A-Fa-f]{6}$/.test(c) ? c + '80' : c;

    /* ── 规则的用户可编辑层 ──
     * 增删改写进 GM，加载时按 id 合并：同 id 保留用户版本，内置新增自动追加，
     */
    const RULES_KEY = 'cfq_rules_v1';
    const normRule = r => ({
        id: String(r.id || ('u' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6))),
        group: r.g || '', name: String(r.n ?? '').trim() || '未命名',
        kw: String(r.k || r.n || ''), color: r.c || '#ff6699',
        medal: r.m || '', off: r.o || '', on: r.on !== false,
    });
    const toRow = r => ({ id: r.id, g: r.group, n: r.name, k: r.kw, c: r.color, m: r.medal, o: r.off, on: r.on });
    const isFanRule = r => r.group === 'V圈';
    // 关注列表匹配用的名称：未显式指定时取第一个关键词（通常为最完整的正式名）
    // 含 & 的表达式（抽奖&@games）不可取首段作为名称，此类规则回退到显示名
    const offName = r => r.off || (r.kw.includes('|') && !r.kw.includes('&') ? r.kw.split('|')[0] : r.name);
    // 作品主名集合，供「抽奖&@games」作与条件；排除粉丝牌与自身以避免递归展开
    const gameWords = all => all.filter(r => r.on && !isFanRule(r) && r.id !== 'g2_bhfamily' && r.id !== 'g7_lottery')
        .map(r => (r.kw.split('|')[0] || '').trim()).filter(Boolean).join('|');

    let RULES = [];

    // 规则串只解析一次：判定阶段直接走数组，避免每次调用重复 split
    const parseRule = str => str.split('&').map(part => {
        const ors = part.split('|').map(k => k.startsWith('!') ? { kw: k.slice(1), neg: true } : { kw: k, neg: false });
        return { neg: ors[0].neg, ors };
    });

    function rebuildRules() {
        const all = state.rules;
        const games = gameWords(all);
        RULES = all.filter(r => r.on).map(r => {
            const rule = r.kw.includes('@games') ? r.kw.replace('@games', games || '不可能出现的占位词') : r.kw;
            return { id: r.id, key: r.id, label: r.name, group: r.group, color: r.color, rule, ast: parseRule(rule) };
        });
    }

    function loadRules() {
        const saved = GM_getValue(RULES_KEY, null);
        const mine = Array.isArray(saved?.rules) ? saved.rules.map(normRule) : DEFAULT_RULES.map(normRule);
        const have = new Set(mine.map(r => r.id));
        const gone = new Set(Array.isArray(saved?.deleted) ? saved.deleted : []);
        for (const d of DEFAULT_RULES.map(normRule)) if (!have.has(d.id) && !gone.has(d.id)) mine.push(d);
        state.rules = mine;
        state.rulesDeleted = [...gone];
        rebuildRules();
    }

    // 规则变更后立即作废全部已算标签：否则楼层保留改名前的旧标签，最长滞留 30 分钟
    function saveRules() {
        GM_setValue(RULES_KEY, { ver: 1, rules: state.rules.map(toRow), deleted: state.rulesDeleted || [] });
        rebuildRules();
        tagCache.clear();
        floorMem.clear();
        buckets.clear();
    }

    // 非重叠计数：split 会为数一个词分配整个数组，这里只走 indexOf
    const countOf = (text, kw) => {
        if (!kw) return 0;
        let n = 0, i = 0;
        while ((i = text.indexOf(kw, i)) >= 0) { n++; i += kw.length; }
        return n;
    };

     /* 规则形如 A&B&!C，| 为或；rule 传 parseRule 结果或原始串。返回 {hits, blocked}。
      * blocked = 正向条件全满足、仅被 !词 拦截，单独报出以免被误判为规则缺失。 */
    function evalRule(text, rule) {
        if (!rule) return null;
        const ast = Array.isArray(rule) ? rule : parseRule(String(rule));
        const hits = [], negated = [];
        let positiveOk = true;
        for (const { neg, ors } of ast) {
            let matched = null;
            for (const o of ors) {
                const at = text.indexOf(o.kw);
                if (at >= 0) { matched = { kw: o.kw, at }; break; }
            }
            if (neg) { if (matched) negated.push(matched); }
            else {
                if (matched) hits.push(matched);
                // 正向条件失败即退出：抽奖&@games 展开后有 30+ 候选词
                else { positiveOk = false; break; }
            }
        }
        if (positiveOk && hits.length && !negated.length) return { hits, blocked: null };
        if (positiveOk && hits.length && negated.length) return { hits: null, blocked: negated };
        return { hits: null, blocked: null };
    }

    /* ── 命中来源归因 ──
     * 语料是整个 data 序列化串，命中可能来自卡片字段而非本人撰写，
     */
    const PATH_LABELS = [
        ['modules.module_dynamic.desc.text', '本人写的动态正文', 'self'],
        ['modules.module_dynamic.rich_content', '本人写的动态正文', 'self'],
        ['modules.module_dynamic.summary', '本人写的动态摘要', 'self'],
        ['modules.module_dynamic.dynamic', '本人动态文案/分享语', 'self'],
        ['modules.module_dynamic.major.opus', '挂载的图文内容', 'attach'],
        ['modules.module_dynamic.major.archive', '挂载的视频信息', 'attach'],
        ['modules.module_dynamic.major.common', '挂载的通用卡片', 'attach'],
        ['modules.module_dynamic.major.draw', '挂载的图集', 'attach'],
        ['modules.module_dynamic.additional', '动态附带的表情/话题/投票', 'attach'],
        ['modules.module_dynamic.rich_text_node', '正文里的表情/话题占位', 'self'],
        ['modules.module_dynamic.origin', '被转发的那条原文', 'attach'],
        ['modules.module_dynamic.topic', '话题标签', 'meta'],
        ['modules.module_dynamic.sku_source', '商品/充电卡片', 'meta'],
        ['modules.module_dynamic.block_user_card', '他人名片（关注/互动的用户）', 'meta'],
        ['modules.module_dynamic.post_update', '投稿更新提示', 'meta'],
        ['modules.module_dynamic.reserve', '预约信息', 'meta'],
        ['modules.module_author', '发布者名片字段', 'meta'],
        ['modules.module_stat', '计数统计', 'meta'],
        ['modules.module_tag', '分区/标签', 'meta'],
        ['modules.module_header', '动态顶部文案', 'meta'],
        ['argument_detail', '投票/活动参数', 'meta'],
        ['card', '用户名片字段', 'meta'],
    ].sort((a, b) => b[0].length - a[0].length);

    const KIND_NAME = { self: '本人文字', attach: '挂载/转发内容', meta: '卡片与元数据' };

    // 未收录路径的兜底：把末级字段名翻成中文，并带上「父级.字段」原文，便于核对来源
    const LEAF_CN = {
        text: '文字', orig_text: '未渲染的原始文字', desc: '描述', title: '标题', name: '名称',
        nickname: '昵称', uname: '用户名', summary: '摘要', content: '内容', uemoji: '表情占位符',
        emoji_text: '表情占位符', area_name: '分区名', from: '来源', reason: '理由',
    };

    const labelOf = path => {
        for (const [pre, label, kind] of PATH_LABELS) if (path.includes(pre)) return { label, kind };
        const segs = path.split('.').filter(Boolean);
        const leaf = segs[segs.length - 1] || '未知';
        const where = segs.length > 1 ? segs.slice(-2).join('.') : leaf;
        return { label: `其它字段：${LEAF_CN[leaf] || leaf}（${where}）`, kind: 'meta' };
    };

    // 纯数字、纯符号与整条链接不计入语料，否则会产生大量无意义命中
    const NOISE_RE = /^(?:[\d\s.,:;、。!\-—_*·#()（）\[\]{}~？?]+|https?:\/\/\S+)$/;

    function collectStrings(node, path, out, limit, meta) {
        if (out.length >= limit || node == null) return;
        if (typeof node === 'string') {
            const s = node.trim();
            if (s.length > 1 && !NOISE_RE.test(s)) out.push({ ...labelOf(path), path, text: node, dyn: meta || null });
            return;
        }
        if (typeof node !== 'object') return;
        if (Array.isArray(node)) { for (let i = 0; i < node.length; i++) collectStrings(node[i], `${path}[${i}]`, out, limit, meta); return; }
        for (const k of Object.keys(node)) collectStrings(node[k], path ? `${path}.${k}` : k, out, limit, meta);
    }

    /* 逐条动态遍历而非整体序列化：每条文本都记录自己所属的动态，
     * 面板才可提供「打开原动态」的直链。置顶（tops）同样计入。 */
    function collectCorpus(raws, limit = 4000) {
        const out = [];
        for (const d of (raws || [])) {
            for (const it of [...(d?.tops || []), ...(d?.items || [])]) {
                if (out.length >= limit) break;
                const a = it?.modules?.module_author || {};
                collectStrings(it, 'item', out, limit, {
                    id: String(it.id_str || it.id || ''),
                    ts: Number(a.pub_timestamp) || 0,
                    name: a.name || '',
                });
            }
        }
        return out;
    }

    const snippet = (text, kw) => text.slice(Math.max(0, text.indexOf(kw) - 12), text.indexOf(kw) + kw.length + 18).replace(/\s+/g, ' ');

    // 统计某个关键词在 records 中出现的来源与次数，附原文片段及其所属动态
    function evidence(records, kw) {
        const bySrc = new Map();
        const links = [];
        let total = 0;
        for (const rec of records) {
            const n = countOf(rec.text, kw);
            if (!n) continue;
            total += n;
            const cur = bySrc.get(rec.label) || { n: 0, kind: rec.kind, sample: '' };
            cur.n += n;
            if (!cur.sample) cur.sample = snippet(rec.text, kw);
            bySrc.set(rec.label, cur);
            // 直链仅给出本人撰写的那几条：挂载卡片中的文本不代表本人发言
            const id = rec.dyn?.id;
            if (id && rec.kind === 'self' && links.length < 3 && !links.some(x => x.id === id)) {
                links.push({ id, ts: rec.dyn.ts, who: rec.dyn.name || '', kw, sample: snippet(rec.text, kw) });
            }
        }
        return { total, srcs: [...bySrc.entries()].sort((a, b) => b[1].n - a[1].n), links };
    }

    // 这里的文本不做转义：why 整串在渲染时统一 esc，提前转义会显示成 &quot;
    const srcLine = (kw, ev) => `「${kw}」${ev.total} 次` + (ev.srcs.length
        ? '\n' + ev.srcs.map(([label, s]) => `   ${s.kind === 'self' ? '★' : '·'} ${label} ×${s.n}${s.sample ? `　“${s.sample}”` : ''}`).join('\n')
        : '（未定位到具体字段）');

    // 命中次数分档：区分「偶尔提及」与「高频出现」，优于二值判定
    const strengthOf = n => n >= 30 ? 5 : n >= 20 ? 4 : n >= 10 ? 3 : n >= 4 ? 2 : 1;
    const STRENGTH_LABEL = ['', '提过一次', '零星提到', '多次提到', '反复出现', '刷屏级'];

    function analyze(records) {
        const text = records.map(r => r.text).join(' ');
        const tags = [], suppressed = [];
        for (const r of RULES) {
            const res = evalRule(text, r.ast);
            if (res.hits) {
                const parts = [], kinds = new Set();
                const links = [];
                let n = 0;
                for (const h of res.hits) {
                    const ev = evidence(records, h.kw);
                    n = Math.max(n, ev.total);
                    parts.push(srcLine(h.kw, ev));
                    for (const s of ev.srcs) kinds.add(s[1].kind);
                    for (const l of ev.links) if (links.length < 3 && !links.some(x => x.id === l.id)) links.push(l);
                }
                const lv = strengthOf(n);
                tags.push({ kind: '推断', name: r.label, color: r.color, ruleKey: r.id, group: r.group,
                    n, level: lv, links,
                    why: parts.join('\n') + `\n来源构成：${[...kinds].map(k => KIND_NAME[k]).join(' + ') || '未知'}` +
                        `\n强度：${STRENGTH_LABEL[lv]}（最多一个词出现 ${n} 次）` +
                        (!kinds.has('self') ? '\n注意：这个词一次都没出现在 TA 自己写的文字里，所以这条标签只能算「相关」，不是「本人说过」。' : '') });
            } else if (res.blocked) {
                suppressed.push({ name: r.label, color: r.color,
                    why: res.blocked.map(b => { const ev = evidence(records, b.kw); return `「${b.kw}」${ev.total} 次（${ev.srcs.map(s => `${s[0]}×${s[1].n}`).join('、') || '无'}）→ 互斥条件不成立`; }).join('\n') });
            }
        }
        if (!tags.length) tags.push({ kind: '推断', name: DEFAULT_TAG.name, color: DEFAULT_TAG.color,
            why: `${RULES.length} 条规则一条都没命中，一条都没命中时挂默认标签。` });
        return { tags, suppressed };
    }

    /* ══════════════ 状态 ══════════════ */

    const blankTab = () => ({ uid: '', pn: 1, src: 'seibun', srcUsed: '', cursors: [''], rows: [], total: null, fail: null, keys: '', busy: false, end: false, cached: false });

    const state = {
        tab: 'query', mid: '', filter: '',
        query: null, videos: null, vidMore: 10,
        comments: blankTab(),
        dm: { ...blankTab(), src: 'vd' },   // 弹幕页：vd=视频弹幕 ld=直播弹幕
        auto: GM_getValue('cfq_auto', true) !== false,   // 楼层自动挂标签，默认开
        liveTags: GM_getValue('cfq_live', true) !== false, // 直播间弹幕行旁的查询按钮，默认开
        dmList: GM_getValue('cfq_dm_list', true) !== false, // 弹幕列表中的查询按钮，默认开
        dmVerify: GM_getValue('cfq_dm_verify', true) !== false, // 多候选时逐个查名片，只留真存在的号，默认开
        dmDeep: GM_getValue('cfq_dm_deep', false) === true, // 反解扩到 10 位：覆盖更多号但候选更杂，默认关
        relay: GM_getValue('cfq_relay', false) === true, // 加速源（中转），默认关
        queryOn: GM_getValue('cfq_query', true) !== false,  // 关闭后只留「成分」与「规则」
        showSettings: false,
        // 规则的用户可编辑副本；loadRules() 在启动时填充，内置表仅作默认值
        rules: [], rulesDeleted: [], ruleEdit: '', ruleQ: '', ruleJSON: '', ruleResetAsk: false,
        ruleMore: false, ruleNewId: '',
        // 面板的三条证据通道：均默认开启，开关收在齿轮弹层里，不占标签栏
        evMedal: GM_getValue('cfq_ev_medal', true) !== false,
        evFollow: GM_getValue('cfq_ev_follow', true) !== false,
        evDynPages: GM_getValue('cfq_ev_dyn', true) !== false,
    };

    const ruleOf = key => RULES.find(r => r.key === key) || null;

    // 规则筛选为本地逐条判定：单条的「正文 + 所属视频标题」是否满足规则
    function ruleHit(row) {
        const r = ruleOf(state.filter);
        if (!r) return true;
        return !!evalRule([row.where, row.message].filter(Boolean).join(' '), r.ast).hits;
    }

     /* 评论页 / 弹幕页均按「UID + 数据源」分桶：切换用户时恢复其上次浏览的页码。
      * 仅存内存，60 桶 LRU；两个页共用一张桶表，src 命名不冲突（seibun|aicu 与 vd|ld）。 */
    const buckets = mkCache({ max: 60 });
    const bucketKey = (uid, src) => `${uid}|${src}`;

    function bucketUse(uid, src = state.comments.src, which = 'comments') {
        const cur = state[which];
        if (cur.uid && (cur.rows.length || cur.total != null)) buckets.set(bucketKey(cur.uid, cur.src), cur);
        state[which] = buckets.get(bucketKey(uid, src)) || { ...blankTab(), uid, src };
        if (/^\d+$/.test(String(uid || ''))) state.mid = String(uid);
    }

    /* ══════════════ 标签页的加载动作 ══════════════ */

    // 先走免签名的裸请求（不进限流队列，响应快），被 -352 拦截后才退回验签慢路
    async function fetchDyn1(uid) {
        const raw = await dynRaw(uid);
        return raw.fail ? await dynSigned(uid) : raw;
    }

    /* 面板用的多页拉取：只取首页等于把召回限制在十几条，翻页靠 data.has_more + offset；
     * 某页失败不作废已取部分，只标注「后续页未取到」。楼层仍走 fetchDyn1 单页。 */
    async function fetchDynPages(uid) {
        const raws = [];
        let offset = '';
        const max = state.evDynPages ? CFG.dynPages : 1;
        for (let i = 0; i < max; i++) {
            const r = i === 0 ? await fetchDyn1(uid) : await dynRaw(uid, offset);
            if (r.fail) return raws.length ? { raws, partial: `第 ${i + 1} 页起没取到：${r.fail}` } : r;
            raws.push(r.data);
            if (!r.data?.has_more || !r.data?.offset) break;
            offset = r.data.offset;
            if (i + 1 < max) await sleep(120 + Math.random() * 120);
        }
        return { raws };
    }

    /* 第二、三条证据通道只在打开单人面板时请求，楼层一条不发。
     * 命中升级为实锤，未命中不下否定结论：关注列表受隐私与截断影响，勋章墙可隐藏，缺席不足以证伪。 */
    // 证据格读不到时的占位：必须带 hits 数组，渲染层直接对它做 map
    const evFail = err => ({ hits: [], medalNote: '证据读取失败：' + String((err && err.message) || err), followNote: '' });

    async function fetchEvidence(mid) {
        const out = { hits: [], medals: null, follows: null, medalNote: '', followNote: '' };
        const jobs = [];
        if (state.evMedal) jobs.push(API.medals(mid).then(r => {
            if (r.fail) out.medalNote = '勋章墙：' + r.fail;
            else if (r.closed) out.medalNote = '勋章墙：TA 设了隐藏（这不等于没有牌）';
            else out.medals = r.list;
        }));
        if (state.evFollow) jobs.push(API.follows(mid).then(r => {
            if (r.hidden) out.followNote = '关注列表：TA 设了隐藏，这条通道本次无结论';
            else if (r.fail) out.followNote = '关注列表：' + r.fail;
            else {
                out.follows = r.list;
                if (r.truncated) out.followNote = `关注列表：只翻到前 ${r.list.length} 条，未命中不代表没关注`;
            }
        }));
        await Promise.all(jobs);
        for (const r of state.rules) {
            if (!r.on) continue;
            const m = r.medal ? (out.medals || []).find(x => x.name && x.name === r.medal) : null;
            const f = (out.follows || []).find(x => `${x.name} ${x.sign} ${x.off}`.includes(offName(r)));
            // 每条命中携带被关注 / 被挂勋章用户的 mid：点击标签查询该用户，而非跳转评论页筛选
            if (m) out.hits.push({ id: r.id, name: r.name, color: r.color, mid: m.mid,
                via: `持有粉丝勋章「${m.name}」Lv${m.level}${m.level >= 21 ? '（21 级以上，基本不用怀疑）' : ''}`,
                strong: m.level >= 21 });
            if (f) out.hits.push({ id: r.id, name: r.name, color: r.color, mid: f.mid,
                via: `关注了「${f.name}」${f.off ? '· ' + f.off : ''}`, strong: f.type === 1 });
        }
        return out;
    }

    /* ── 楼层 DOM 中页面自己下发的信息，读出来可省一次请求 ──
     * 只取稳定三项：昵称、等级（level_N.svg 解析）、头像 URL。取不到留空等 card 补，不做推测。 */

    function readFloorDom(root, uid) {
        if (!root || !uid) return;
        // 已缓存则跳过：滚动同样触发 scan，无此守卫会导致每次滑动都对整屏执行 getComputedStyle
        const had = domProfile.get(String(uid));
        if (had?.name && had?.face) return;
        const info = root.querySelector('#user-name') ? root : (root.querySelector('bili-comment-user-info')?.shadowRoot || root);
        const name = info.querySelector('#user-name')?.textContent?.trim() || '';
        const m = /level[_-]?(\d+)/.exec(info.querySelector('#user-level img')?.getAttribute('src') || '');
        let face = '';
        for (const el of (root.querySelector('bili-avatar')?.shadowRoot?.querySelectorAll('div') || [])) {
            const g = /^url\("?(.+?)"?\)$/.exec(getComputedStyle(el).backgroundImage);
            if (g && /bfs\/(face|upload)\//.test(g[1])) { face = g[1]; break; }
        }
        if (!name && !m && !face) return;
        const old = domProfile.get(uid) || {};
        domProfile.set(uid, { name: name || old.name || '', level: m ? +m[1] : old.level, face: face || old.face || '' });
    }

    // card 单接口即可支撑首屏：等级/性别/签名/认证/粉丝/关注/获赞/投稿数均在其中
    const profileFromCard = (card, mid) => {
        const c = card?.card || {};
        const lean = domProfile.get(String(mid)) || {};
        return {
            mid: String(mid), name: c.name || lean.name || '', face: c.face || lean.face || '',
            level: c.level_info?.current_level ?? lean.level,
            sex: c.sex, sign: c.sign || '', follower: card?.follower ?? c.fans, following: card?.attention,
            likes: card?.like_num, official: c.official_verify?.title || '',
        };
    };

    // 首屏之后在后台补的三格：生日 / 精确获赞 / 总播放量。
    // 这些字段需 WBI 签名并走限流队列，不参与首屏计时，返回后自动补全。
    async function fetchExtra(mid) {
        // 三个接口互不依赖，并发执行（bili 队列内间隔约 150ms），优于串行
        const [info, stat, up] = await Promise.all([API.accInfo(mid), API.relation(mid), API.upstat(mid)]);
        const p = {};
        if (!info.__fail) {
            p.birthday = info.birthday || '';
            if (info.level != null) p.level = info.level;
            if (info.sex) p.sex = info.sex;
            if (info.sign) p.sign = info.sign;
            const off = info.official?.title || info.official?.desc;
            if (off) p.official = off;
        }
        if (!stat.__fail) { p.follower = stat.follower; p.following = stat.following; }
        if (!up.__fail) { p.likes = up.likes; p.views = up.archive?.view; }
        return { profile: p, fail: info.__fail || stat.__fail || up.__fail || null };
    }

    function applyCorpus() {
        const q = state.query, c = q.card?.card || {};
        q.profile = { ...profileFromCard(q.card, q.mid), ...(q.extra || {}) };
        q.dynItems = (q.dynRaws || []).flatMap(d => d.items || []);
        // 名片三项为本人撰写内容，排在最前，来源归为「本人」
        const records = [{ label: '昵称/签名/简介', kind: 'self', path: 'card', text: [c.name, c.sign, c.description].filter(Boolean).join(' ') }];
        records.push(...collectCorpus(q.dynRaws));
        const { tags, suppressed } = analyze(records);
        // 动态一条都未取到时，语料仅剩「昵称 / 签名 / 简介」；
        // 此时的命中来自个人资料而非发言，不构成证据，需在面板明确标注。
        const thin = !(q.dynRaws || []).length;
        q.corpusThin = thin;
        if (thin) for (const t of tags) {
            if (t.name === DEFAULT_TAG.name) continue;
            t.why += `\n⚠ 动态 0 条（${q.dynFail ? '接口报错：' + q.dynFail : '未取到'}），这条只凭昵称/签名/简介判定，可信度很低。重新点「查询」重试。`;
        }
        q.guess = tags; q.suppressed = suppressed;
        // 动态接口报错时「一条都没命中」并不成立：读到的语料是 0，与楼层同一口径挂失败标签
        if (q.dynFail && !q.dynRaws?.length && tags.length === 1 && tags[0].name === DEFAULT_TAG.name)
            q.guess = [{ name: ERROR_TAG.name, color: ERROR_TAG.color, why: q.dynFail }];
        q.corpusCount = q.dynItems.length;
        q.corpusFields = records.length;
        q.corpusSelf = records.filter(r => r.kind === 'self').length;
        render();
    }

    // seibun 的 resolve-user 可将「用户名 / space 链接 / b23.tv 短链」解析为 UID，
    // 免去手动进入空间页取号
    async function resolveUid(input) {
        const s = String(input || '').trim();
        if (/^\d+$/.test(s)) return { uid: s };
        const m = s.match(/space\.bilibili\.com\/(\d+)/);
        if (m) return { uid: m[1] };
        const r = await get(`${via('seibun', API_PATH.resolve)}?query=${encodeURIComponent(s)}`, { referer: EP.seibun.direct + '/' }, 'seibun');
        if (r.json?.uid) return { uid: String(r.json.uid), via: 'seibun 用户名解析' };
        return { fail: r.fail || r.json?.error?.message || '没解析出 UID（输入需是 UID、空间链接、短链或完整用户名）' };
    }

    let querySeq = 0;      // 后台补数据回来时用它判断「人还在不在这一页」

    // note 只用于面板头部标注「这次是谁触发的」，弹幕候选切换靠它让两次点击长出区别
    async function runQuery(raw, note) {
        const me = ++querySeq;
        const want = String(raw || '').trim();
        state.tab = 'query';
        // 换查询对象即换上下文：清掉上一个人的规则筛选，避免它残留在新数据上
        state.filter = '';
        markActive(null);                             // 描边只跟「最后一次查询」，从弹幕/输入框查的也要把它摘掉
        state.query = { mid: want, loading: true, note: note || '' };
        render();                                     // 点下去立刻出面板骨架，不在空白里转圈
        const got = await resolveUid(want);
        if (got.fail) { state.query = { mid: want, error: got.fail }; return render(); }
        const mid = got.uid;
        state.mid = mid;
        state.videos = null;
        // 换人时评论页与弹幕页的分桶都要跟着换：否则弹幕框里还是上一个人的 UID
        bucketUse(mid);
        bucketUse(mid, state.dm.src, 'dm');
        const cache = personCache.get(mid);
        state.query = { mid, resolved: got.via || null, card: cache?.card || null,
            dynRaws: cache?.raws || null, extra: cache?.extra || null, loading: true, note: note || '' };
        render();

        // card 与动态互不依赖：动态先行（不占限流队列），card 在队列中排队，先返回者先渲染
        const dynP = state.query.dynRaws ? null : fetchDynPages(mid);
        if (!state.query.card) {
            const card = await API.card(mid);
            if (me !== querySeq) return;
            state.query.card = card;
            personCache.patch(mid, { card });
            applyCorpus();
        }
        if (dynP) {
            const d = await dynP;
            if (me !== querySeq) return;
            if (d.fail) state.query.dynFail = d.fail;
            else {
                state.query.dynRaws = d.raws;
                state.query.dynPartial = d.partial || '';
                personCache.patch(mid, { raws: d.raws });
            }
        }
        if (me !== querySeq) return;
        state.query.loading = false;
        applyCorpus();

        // 勋章墙 / 关注列表与资料补全互不依赖，各自后台加载，先返回者先渲染
        if (!state.query.ev) {
            const ev = cache?.ev || null;
            if (ev) state.query.ev = ev;
            else fetchEvidence(mid).then(r => {
                if (me !== querySeq) return;
                state.query.ev = r;
                personCache.patch(mid, { ev: r });
                render();
            }).catch(err => {
                if (me !== querySeq) return;
                // 不 catch 的话这一格永远停在「读取中…」，与失败要响的原则相反
                state.query.ev = evFail(err);
                render();
            });
        }

        // 三格签名接口的数据：首屏后在后台排队补齐，返回即填充，不阻塞其他请求
        if (state.query.extra) { render(); return; }
        state.query.extraLoading = true;
        fetchExtra(mid).then(e => {
            if (me !== querySeq) return;
            state.query.extraLoading = false;
            state.query.extraFail = e.fail;
            if (Object.keys(e.profile).length) {
                state.query.extra = e.profile;
                personCache.patch(mid, { extra: e.profile });
            }
            applyCorpus();
        }).catch(err => {
            if (me !== querySeq) return;
            // 同上：补全失败要让「补全中…」停下来并说出原因
            state.query.extraLoading = false;
            state.query.extraFail = String((err && err.message) || err);
            render();
        });
    }

    // aicu v3 行 → 统一行结构
    const fromAicu = j => {
        const d = j?.code === 0 ? j.data : null;
        if (!d) return null;
        return {
            rows: (d.replies || []).map(x => ({
                rpid: String(x.rpid || ''), time: Number(x.time || x.ctime || 0), message: x.message || '',
                rank: Number(x.rank) || 0, uname: '', likes: null,
                href: x.dyn?.type === 12 ? `https://www.bilibili.com/read/cv${x.dyn.oid}#reply${x.rpid}`
                    : x.dyn?.type === 1 || x.oid ? `https://www.bilibili.com/video/av${x.dyn?.oid || x.oid}#reply${x.rpid}`
                    : `https://t.bilibili.com/${x.dyn?.oid || x.oid}#reply${x.rpid}`,
                where: `type ${x.dyn?.type ?? '?'} · oid ${x.dyn?.oid || x.oid || '?'}`,
            })),
            total: Number(d.cursor?.all_count) || null, end: !!d.cursor?.is_end, next: null,
        };
    };

    // seibun 行 → 同一套行结构（直接给出 bvid，跳转比 av 更准确）
    const fromSeibun = j => {
        if (!Array.isArray(j?.comments)) return null;
        return {
            rows: j.comments.map(x => {
                const t = x.target || {};
                const base = t.type === 'video' && t.bvid ? `https://www.bilibili.com/video/${t.bvid}`
                    : t.type === 'opus' || t.type === 'dynamic' ? `https://t.bilibili.com/${t.oid || t.id || ''}`
                    : `https://www.bilibili.com/video/${t.bvid || ''}`;
                return {
                    rpid: String(x.rpid || ''), time: Number(x.ctime || 0), message: x.raw_message || '',
                    rank: Number(x.parent) > 0 ? 2 : 1, uname: x.uname || '', likes: Number(x.like_count) || 0,
                    href: `${base}#reply${x.rpid}`,
                    where: t.bvid ? `${t.bvid} ${t.title || ''}` : (t.title || t.type || ''),
                };
            }),
            total: Number(j.total_count) || null, end: !j.next_cursor, next: j.next_cursor || null,
        };
    };

    async function loadComments(page) {
        const t = state.comments;
        if (!/^\d+$/.test(String(t.uid || ''))) { t.fail = '请先填 UID（或在「成分」里查一个人/用户名）'; return render(); }
        if (t.busy) return;
        const pn = page || 1;
        t.busy = true; t.fail = null; t.keys = '';
        if (pn === 1) { t.rows = []; t.total = null; t.cursors = ['']; }
        render();
        const cursor = t.cursors[pn - 1] ?? null;
        if (t.src === 'seibun') {
            const q = { uid: t.uid, limit: CFG.seiLimit, order: 'desc' };
            if (cursor) q.cursor = cursor;
            t.cands = [{ name: 'seibun', lane: 'seibun', key: `${lineTag()}:sei:${t.uid}:${cursor || 'first'}:${CFG.seiLimit}`, url: `${via('seibun', API_PATH.comments)}?${qsBuild(q)}`, parse: fromSeibun }];
        } else {
            // v3 免票接口，参数形式与既有版本一致
            t.cands = [{ name: 'aicu', lane: 'aicu', opts: { timeout: CFG.aicuTimeout }, key: `${lineTag()}:ai3:${t.uid}:${pn}:${CFG.ps}`, url: `${via('aicu', API_PATH.reply)}?${qsBuild({ uid: t.uid, pn, ps: CFG.ps, mode: 0 })}`, parse: fromAicu }];
        }
        const r = await indexSearch(t.cands);
        t.busy = false;
        // 请求期间用户可能已切换对象：结果仍写入其对应的桶，但不改动当前视图
        const paint = () => { if (state.comments === t) render(); };
        if (r.fail) { t.fail = r.fail; return paint(); }
        const d = r.data;
        // 分页：每页仅展示当页数据，不累加；回看上一页依赖一小时缓存，不重复请求
        t.rows = d.rows;
        t.total = d.total; t.end = d.end; t.pn = pn; t.cached = !!r.cached; t.srcUsed = r.src;
        if (d.next && !t.cursors[pn]) t.cursors[pn] = d.next;   // 下一页要用服务端给的 cursor
        if (!d.rows.length && pn === 1) t.keys = '响应里没有可解析的行数组';
        paint();
    }

    /* ── 弹幕（仅 aicu v4）：视频行 {id,oid,ctime(秒),progress(毫秒),content}，跳转用 av+dmid；
     */
    const toSec = v => { const n = Number(v) || 0; return n > 1e11 ? Math.round(n / 1000) : n; };

    const fromVd = j => {
        const d = j?.code === 0 ? j.data : null;
        if (!d) return null;
        return {
            rows: (d.videodmlist || []).map(x => ({
                rpid: String(x.id || ''), time: toSec(x.ctime), message: x.content || '',
                rank: 0, uname: '', likes: null,
                href: `https://www.bilibili.com/video/av${x.oid}/?p=1&dmid=${x.id}`,
                where: `av${x.oid || '?'} · 视频内 ${Math.round((Number(x.progress) || 0) / 1000)}s`,
            })),
            total: Number(d.cursor?.all_count) || null, end: !!d.cursor?.is_end, next: null,
        };
    };

    const fromLd = j => {
        const d = j?.code === 0 ? j.data : null;
        if (!d) return null;
        const rows = [];
        for (const g of (d.list || [])) {
            const ri = g.roominfo || {};
            for (const x of (g.danmu || [])) rows.push({
                rpid: '', time: toSec(x.ts), message: x.text || '',
                rank: 0, uname: x.uname || '', likes: null,
                href: ri.roomid ? `https://live.bilibili.com/${ri.roomid}` : '',
                where: `${ri.roomname || '直播间'} · 主播 ${ri.upname || ri.upuid || ''}`,
            });
        }
        return { rows, total: Number(d.cursor?.all_count) || null, end: !!d.cursor?.is_end, next: null };
    };

    const DM = {
        vd: { name: '视频弹幕', path: 'getvideodm', parse: fromVd, tip: 'aicu 自己标注：受匹配算法限制，归属可能不准。' },
        ld: { name: '直播弹幕', path: 'getlivedm', parse: fromLd, tip: '按直播间分组，点行进那个直播间。' },
    };

    async function loadDanmu(page) {
        const t = state.dm, s = DM[t.src];
        if (!/^\d+$/.test(String(t.uid || ''))) { t.fail = '请先填 UID（或在「成分」里查一个人）'; return render(); }
        if (t.busy) return;
        const pn = page || t.pn || 1;
        const key = `${lineTag()}:dm4:${t.src}:${t.uid}:${pn}:${CFG.dmPs}`;
        t.busy = true; t.fail = null; t.keys = '';
        if (pn === 1) { t.rows = []; t.total = null; }
        render();
        // 请求期间用户可能已切换对象：结果写入其对应的桶，仅当视图仍指向该对象时重绘
        const paint = () => { if (state.dm === t) render(); };
        const hit = dmCache.get(key);
        if (hit) { Object.assign(t, hit, { busy: false, cached: true }); return paint(); }
        const r = await aicuV4(s.path, { uid: t.uid, pn, ps: CFG.dmPs, keyword: '', need_count: true });
        t.busy = false;
        if (r.fail) { t.fail = r.fail; return paint(); }
        const d = s.parse(r.json);
        if (!d) { t.keys = Object.keys(r.json?.data || {}).join(', ') || '无 data'; return paint(); }
        const slim = { rows: d.rows, total: d.total, end: d.end, pn, cached: false, srcUsed: 'aicu', fail: null, keys: '' };
        dmCache.set(key, slim);
        Object.assign(t, slim, { busy: false });
        if (!d.rows.length && pn === 1) t.keys = '响应里没有行（这个 UID 在 aicu 的索引里没有此类弹幕）';
        paint();
    }

    /* ══════════════ 渲染 ══════════════ */

    // 成分标签只做展示，不携带 data-rule、不触发跳转：跳转入口由「评论」标签页的筛选按钮承担
    const chip = t => `<span class="chip" title="${esc(t.group || '')}" style="color:${esc(t.color)};border-color:${esc(t.color)}">${esc(t.name)}${t.level > 1 ? ' ×' + t.n : ''}</span>`;
    const kv = (k, v) => `<b>${esc(k)}</b><span>${v}</span>`;
    const link = (href, inner) => `<a class="item" href="${esc(href)}" target="_blank" rel="noopener noreferrer">${inner}</a>`;

    /* 命中动态直链只在面板内展开，不进 slim、不进 GM：楼层缓存覆盖数千人，挂原文会使存储无上界。 */
    function linkBlock(q) {
        const seen = new Map();
        for (const t of (q.guess || [])) for (const l of (t.links || [])) if (!seen.has(l.id)) seen.set(l.id, l);
        if (!seen.size) return '';
        return `<div class="lk">命中原文：${[...seen.values()].map(l =>
            `<a href="https://t.bilibili.com/${esc(l.id)}" target="_blank" rel="noopener noreferrer">「${esc(l.kw)}」→ ${esc(l.sample)}${l.ts ? ' · ' + fmtTs(l.ts) : ''}</a>`).join('')}</div>`;
    }

    // 关注 / 勋章两条通道的结果：命中是加分项，未命中不下结论
    function evidenceBlock(q) {
        if (!state.evMedal && !state.evFollow) return '';
        const e = q.ev;
        if (!e) return '<h4>关注 / 勋章证据</h4><div class="t">读取中…</div>';
        const notes = [e.medalNote, e.followNote].filter(Boolean).map(n => `<div class="t">${esc(n)}</div>`).join('');
        // 证据标签不携带 data-rule：其来源不是关键词命中，跳转到评论页筛选没有意义。
        // 点击行为改为查询该被关注 / 被挂勋章的用户本身，与插件主动作一致。
        const hits = e.hits.length
            ? e.hits.map(h => `<span class="chip"${h.mid ? ` data-act="ev-goto" data-mid="${esc(h.mid)}"` : ''} style="color:${esc(h.color)};border-color:${esc(h.color)}"
                title="${h.mid ? '点开查这个人的成分' : ''}">${h.strong ? '★ ' : ''}${esc(h.name)} · ${esc(h.via)}</span>`).join('')
            : '<span class="un">这两条通道没有新命中</span>';
        return `<h4>关注 / 勋章证据</h4>
          <div class="un">命中只给上面的标签加实锤；未命中不代表没成分（关注列表可能被隐藏、勋章墙可能关了）。</div>
          ${notes}<div>${hits}</div>`;
    }

    // 规则筛选：一排按钮，「全部」即不筛选。仅列出本页有命中的规则，避免全量规则表淹没列表。
    function filterSelect(rows) {
        const hit = [];
        for (const r of RULES) {
            const n = rows.reduce((a, row) => a + (evalRule([row.where, row.message].filter(Boolean).join(' '), r.ast).hits ? 1 : 0), 0);
            if (n) hit.push({ ...r, n });
        }
        // 由「成分」页带入的筛选规则若在本页零命中，只在这一页确实有数据时才保留；
        // 否则切换查询对象后，上一个人的筛选牌会残留在空列表上
        const active = rows.length ? ruleOf(state.filter) : null;
        if (active && !hit.some(x => x.key === active.key)) hit.unshift({ ...active, n: 0 });
        if (!hit.length) return `<div class="un">本页 ${rows.length} 条无规则命中</div>`;
        return `<div class="frow"><span class="fb${state.filter ? '' : ' on'}" data-act="filter-set" data-id="" style="--c:#909399">全部</span>
          ${hit.map(r => `<span class="fb${state.filter === r.key ? ' on' : ''}" data-act="filter-set" data-id="${esc(r.key)}" style="--c:${esc(r.color)}">${esc(r.label)} ${r.n}</span>`).join('')}</div>`;
    }

    // 返回 code:0 却未解析出行时，回显响应的真实字段名（凭猜测构造字段不可靠）
    const keysLine = t => (!t.rows.length && t.keys)
        ? `<div class="warn">响应结构未识别，data 字段：<b>${esc(t.keys)}</b></div>` : '';

    // 翻页条：固定在面板底部，两个按钮 + 一行状态；跳转输入框仅对 pn 型数据源开放（aicu 评论、两类弹幕），seibun 为服务端 cursor，不支持跳转
    function pager(t, act) {
        if (!t.rows.length && t.total == null && !t.busy) return '';
        const pages = t.total ? Math.max(1, Math.ceil(t.total / (DM[t.src] ? CFG.dmPs : CFG.ps))) : 0;
        return `<div class="pg">
          <button data-act="${act}" data-pn="${t.pn - 1}" ${t.pn <= 1 ? 'disabled' : ''}>← 上一页</button>
          <button class="pri" data-act="${act}" data-pn="${t.pn + 1}" ${t.end ? 'disabled' : ''}>下一页 →</button>
          ${t.src !== 'seibun' && pages > 1 ? `<input id="jumppn" type="number" min="1" max="${pages}" value="${t.pn}"><button data-act="${act}-jump">跳转</button>` : ''}
          <span class="t">第 ${t.pn} 页${pages ? ` / 约 ${pages} 页` : ''} · 本页 ${t.rows.length} 条${t.total != null ? ` · 共 ${num(t.total)} 条` : ''}${t.cached ? ' · 缓存' : ''}</span>
        </div>`;
    }

    /* 设置弹层由齿轮展开；三条证据通道默认开启且只作用于单人面板，楼层自动标签始终只发一条动态请求。 */
    const swPill = (label, on, act, tip) => `<div class="si" title="${esc(tip || '')}">
        <span>${esc(label)}</span><span class="sw${on ? ' on' : ''}" data-act="${act}">${on ? '开' : '关'}</span></div>`;

    function settingsPop() {
        return `<div class="set">
          <div class="sg">总开关</div>
          ${swPill('查询功能', state.queryOn, 'set-query', '关闭后只保留「成分」与「规则」两个标签页，其余隐藏')}
          ${swPill('数据源加速', state.relay, 'relay-toggle', '尝试中转，随时失效')}
          <div class="sn">默认关，切换数据源</div>
          <div class="sg">查询入口挂载</div>
          ${swPill('评论区标签', state.auto, 'auto-toggle', '在评论区楼层旁自动挂成分标签')}
          ${swPill('直播页查询按钮', state.liveTags, 'live-toggle', '在直播间弹幕栏的昵称旁挂查询按钮，只挂按钮不发请求')}
          ${swPill('弹幕列表查询', state.dmList, 'dm-list-toggle', '视频页播放器弹幕列表：悬停出现查询按钮，点了才拉那一段弹幕')}
          <div class="sg">弹幕发送者反查</div>
          ${swPill('不猜号', state.dmVerify, 'dm-verify-toggle', '一条弹幕常常同时对应好几个 UID。开着时会挨个查一遍名片，只留真有其人的；一个都对不上就直说查不到，不会硬塞给你一个疑似号。只在出现多个候选时才多发几个请求')}
          ${swPill('多认 10 位新号', state.dmDeep, 'dm-deep-toggle', '关：只认 9 位以内的老号，实测一条弹幕 64% 能认出来。开：连 10 位号一起认，能认出的升到 98%，代价是一条弹幕会同时冒出更多疑似号，要靠上面的「不猜号」收。16 位新号两种都认不出')}
          <div class="sg">单人证据通道</div>
          ${swPill('勋章墙', state.evMedal, 'ev-evMedal', '读取目标持有的粉丝勋章，牌名精确匹配才算实锤')}
          ${swPill('关注列表', state.evFollow, 'ev-evFollow', '读取目标的关注列表做名字匹配，可能被隐私隐藏且需翻页')}
          ${swPill('动态翻页', state.evDynPages, 'ev-evDynPages', '查单人时读取最近 3 页动态，否则只读 1 页')}
        </div>`;
    }

    function tabQuery() {
        const q = state.query;
        const input = `<div class="row"><input id="mid" placeholder="UID" value="${esc(state.mid)}">
          <button class="pri" data-act="query">查询</button>
          ${q ? '<button data-act="videos">投稿列表</button>' : ''}
          </div>`;
        if (!q) return input;
        if (q.error) return input + `<div class="warn">${esc(q.error)}</div>`;
        if (q.loading && !q.card) {
            // 楼层 DOM 已有的昵称/头像/等级先行填充，缺失部分显示骨架
            const lean = profileFromCard(null, q.mid);
            return input + `<div class="hd">${lean.face ? `<img src="${esc(lean.face)}">` : '<div class="sk" style="width:38px;height:38px;border-radius:50%"></div>'}
              <div><div class="nm">${esc(lean.name) || '<span class="t">读取中…</span>'}</div>
              <div class="t">UID ${esc(q.mid)}${lean.level != null ? ' · LV' + lean.level : ''}${q.note ? ' · ' + esc(q.note) : ''}</div></div></div>
              <div class="sk" style="width:70%"></div><div class="sk" style="width:90%"></div><div class="sk" style="width:55%"></div>`;
        }
        const p = q.profile || {}, c = q.card?.card || {};
        return input + `
        <div class="hd"><img src="${esc(p.face || '')}"><div><div class="nm">${esc(p.name) || '（无资料）'}</div><div class="t">UID ${esc(q.mid)}${q.resolved ? ' · ' + esc(q.resolved) : ''}${q.note ? ' · ' + esc(q.note) : ''}</div></div></div>
        ${q.warn ? '<div class="warn">' + esc(q.warn) + '</div>' : ''}
        <h4>推断 · 关键词命中</h4>
        <div class="un">语料：动态 ${q.corpusCount || 0} 条 / ${num(q.corpusFields)} 个文本字段${q.dynRaws?.length > 1 ? ` · 翻了 ${q.dynRaws.length} 页` : ''}（★=TA 自己写的，·=卡片挂载字段）${q.corpusThin ? ' · <b>动态 0 条，下面只依据昵称签名</b>' : ''}${q.dynPartial ? ' · <b>' + esc(q.dynPartial) + '</b>' : ''}${q.dynFail ? ' · <b>动态报错：' + esc(q.dynFail) + '</b>' : ''}</div>
        ${q.guess?.length ? q.guess.map(t => `${chip(t)}<div class="why">${esc(t.why)}</div>`).join('') : '<span class="un">未命中关键词</span>'}
        ${linkBlock(q)}
        ${evidenceBlock(q)}
        ${q.suppressed?.length ? `<h4>被互斥条件挡掉的</h4>
          ${q.suppressed.map(s => `<div class="sup">${esc(s.name)} — ${esc(s.why)}</div>`).join('')}` : ''}
        <h4>用户信息${q.extraLoading ? ' <span class="t">补全中…</span>' : ''}</h4><div class="kv">
          ${kv('用户名', esc(p.name) || '—')}${kv('UID', esc(q.mid))}
          ${kv('等级', p.level != null ? 'LV' + p.level : '—')}${kv('性别', esc(p.sex) || '—')}
          ${kv('签名', esc(p.sign) || '—')}${kv('认证', esc(p.official) || '—')}
          ${kv('生日', esc(p.birthday) || '—')}${kv('粉丝数', num(p.follower))}
          ${kv('关注数', num(p.following))}${kv('获赞数', num(p.likes))}
          ${kv('总播放量', num(p.views))}${kv('投稿数', num(state.videos?.total ?? q.card?.archive_count))}
        </div>
        ${q.extraFail && !q.extraLoading ? `<div class="t">生日/获赞/总播放量 未取到：${esc(q.extraFail)}</div>` : ''}
        ${state.videos ? `<h4>投稿视频 · 共 ${num(state.videos.total)} 个，这里取最近 ${state.videos.list.length} 个</h4>
          ${state.videos.fail ? `<div class="warn">${esc(state.videos.fail)}</div>` : ''}
          ${state.videos.list.slice(0, state.vidMore).map((v, i) => link(`https://www.bilibili.com/video/${v.bvid}`,
            `<div>${i + 1}. ${esc(v.title)}</div><div class="t">${esc(v.bvid)} · 播放 ${num(v.play)} · ${fmtTs(v.created)}</div>`)).join('') || '<div class="un">无投稿视频</div>'}
          ${state.videos.list.length > state.vidMore ? `<div class="row"><button data-act="videos-more">展开更多（还有 ${state.videos.list.length - state.vidMore} 个）</button></div>` : ''}` : ''}
`;
    }

    function tabComments() {
        const t = state.comments;
        const shown = t.rows.filter(r => ruleHit(r));
        const owner = t.uid ? `<div class="t">评论 · UID ${esc(t.uid)}${t.srcUsed ? ` · 数据源：${esc(t.srcUsed)}` : ''}${t.uid !== state.mid && state.mid ? ' · 不是当前查询的人' : ''}</div>` : '';
        return `<div class="row"><input id="uid-comments" placeholder="UID" value="${esc(t.uid || state.mid)}">
          <button class="pri" data-act="go-comments">查询</button></div>
          <div class="row"><select id="src">
            <option value="seibun"${t.src === 'seibun' ? ' selected' : ''}>数据源：seibun</option>
            <option value="aicu"${t.src === 'aicu' ? ' selected' : ''}>数据源：aicu</option>
          </select></div>
          ${owner}
          <div class="un">${esc(AICU_NOTE)}</div>
          ${filterSelect(t.rows)}
          ${state.filter ? `<div class="t">按「${esc(ruleOf(state.filter)?.label || state.filter)}」筛选：本页 ${t.rows.length} 条中命中 ${shown.length} 条</div>` : ''}
          ${t.fail ? `<div class="warn">${esc(t.fail)}</div>` : ''}${keysLine(t)}
          <div class="list${t.busy ? ' dim' : ''}">${shown.length ? shown.map(r => link(r.href,
            `<div>${esc(r.message)}</div><div class="t">${fmtTs(r.time)} · ${r.rank === 1 ? '一级' : '二级'} · ${r.likes != null ? '赞 ' + num(r.likes) + ' · ' : ''}rpid ${esc(r.rpid)}${r.where ? ' · ' + esc(r.where.slice(0, 46)) : ''}</div>`)).join('')
            : `<div class="un">${t.rows.length ? '当前筛选下无匹配' : t.busy ? '加载中…' : '暂无数据'}</div>`}</div>
          ${pager(t, 'pg-comments')}`;
    }

    // 弹幕数据仅 aicu v4 提供，故无数据源下拉，只有「视频 / 直播」二选一
    function tabDanmu() {
        const t = state.dm, s = DM[t.src] || DM.vd;
        const shown = t.rows.filter(r => ruleHit(r));
        const owner = t.uid ? `<div class="t">${esc(s.name)} · UID ${esc(t.uid)} · 数据源：aicu${t.uid !== state.mid && state.mid ? ' · 不是当前查询的人' : ''}</div>` : '';
        return `<div class="row"><input id="uid-dm" placeholder="UID" value="${esc(t.uid || state.mid)}">
          <button class="pri" data-act="go-dm">查询</button></div>
          <div class="row"><select id="dm-src">
            <option value="vd"${t.src === 'vd' ? ' selected' : ''}>视频弹幕</option>
            <option value="ld"${t.src === 'ld' ? ' selected' : ''}>直播弹幕</option>
          </select></div>
          ${owner}
          <div class="un">${esc(AICU_NOTE)}</div>
          <div class="un">${esc(s.tip)} 一页 ${CFG.dmPs} 条 = 取号 + 查询两个请求（票只能用一次），只在你点「查询」时才发。</div>
          ${filterSelect(t.rows)}
          ${state.filter ? `<div class="t">按「${esc(ruleOf(state.filter)?.label || state.filter)}」筛选：本页 ${t.rows.length} 条中命中 ${shown.length} 条</div>` : ''}
          ${t.fail ? `<div class="warn">${esc(t.fail)}</div>` : ''}${keysLine(t)}
          <div class="list${t.busy ? ' dim' : ''}">${shown.length ? shown.map(r => {
            const inner = `<div>${esc(r.message)}</div><div class="t">${fmtTs(r.time)}${r.uname ? ' · ' + esc(r.uname) : ''}${r.where ? ' · ' + esc(r.where.slice(0, 46)) : ''}</div>`;
            return r.href ? link(r.href, inner) : `<div class="item">${inner}</div>`;
          }).join('')
            : `<div class="un">${t.rows.length ? '当前筛选下无匹配' : t.busy ? '取号并查询中…' : '暂无数据'}</div>`}</div>
          ${pager(t, 'pg-dm')}`;
    }

    // aicu 的三个页面共用读取 URL ?uid= 的入口，因此带上 uid 即为已填入并自动查询。
    // 这个 tab 只是开 www.aicu.cc 的网页，插件本身不发任何接口请求。
    const AICU_PAGES = [
        ['/reply', '查评论'],
        ['/videodanmu', '查视频弹幕'],
        ['/livedanmu', '查直播弹幕'],
    ];

    function tabAicu() {
        const uid = state.comments.uid || state.mid || '';
        return `<div class="row"><input id="uid-aicu" placeholder="UID" value="${esc(uid)}">
          <button data-act="aicu-set">填入</button></div>
          <div class="row">${AICU_PAGES.map(([p, n]) => `<button class="pri" data-act="aicu" data-p="${p}">${n}</button>`).join('')}</div>
          <div class="un">${esc(AICU_NOTE)}</div>
          ${uid ? `<div class="un">跳转 aicu.cc 站内检索，UID 随链接带入。这个页只是开它的网页，插件本身不发请求。</div>`
                : '<div class="warn">缺 UID，先在「成分」查一个人或手动填入。</div>'}`;
    }

    /* ══════════════ 规则页：增删改与导入导出 ══════════════
     * 即时落盘：输入框失焦即写 GM 并清标签缓存，无独立保存步骤。
     */
    const RULE_FIELDS_BASE = [['name', '显示名'], ['kw', '匹配词（| 或 · & 与 · @games = 任一作品名）'], ['color', '颜色']];
    const RULE_FIELDS_MORE = [
        ['group', '分组（标签归类，规则页里按它折叠）'],
        ['medal', '粉丝勋章名（勋章名精确匹配才算实锤）'],
        ['off', '关注列表匹配名（留空 = 用第一个关键词）']];
    const rfInput = (f, edit) => `<label${f[0] === 'kw' ? ' class="wide"' : ''}>${esc(f[1])}<input data-rf="${f[0]}" data-id="${esc(edit.id)}" value="${esc(edit[f[0]] ?? '')}"></label>`;

    function tabRules() {
        const q = state.ruleQ.trim().toLowerCase();
        const rows = state.rules.filter(r => !q || `${r.name} ${r.kw} ${r.group} ${r.medal} ${r.off}`.toLowerCase().includes(q));
        const edit = state.ruleEdit ? state.rules.find(r => r.id === state.ruleEdit) : null;
        return `<div class="row">
            <input id="ruleq" placeholder="搜索显示名 / 关键词" value="${esc(state.ruleQ)}">
            <button data-act="rules-new">新增</button>
            <button data-act="rules-export">导出</button>
            <button data-act="rules-import">导入</button>
            ${state.ruleResetAsk ? '<button class="pri" data-act="rules-reset-yes">确定恢复默认？</button>'
                : '<button data-act="rules-reset">恢复默认</button>'}</div>
          <div class="un">共 ${state.rules.length} 条 · 已启用 ${state.rules.filter(r => r.on).length} 条<br>
            配置修改后立即生效，同时清除本地标签缓存。规则库升级时自动合并新增条目，已删除的条目不再恢复。</div>
          ${edit ? `<div class="rf">
            ${RULE_FIELDS_BASE.map(f => rfInput(f, edit)).join('')}
            ${state.ruleMore ? RULE_FIELDS_MORE.map(f => rfInput(f, edit)).join('') : ''}
            <div class="row rfbtn">
              <button class="pri" data-act="rules-close">完成</button>
              ${edit.id === state.ruleNewId ? '<button data-act="rules-cancel">取消新增</button>' : ''}
              <button data-act="rules-more">${state.ruleMore ? '收起' : '更多字段'}</button></div></div>` : ''}
          ${state.ruleJSON ? `<textarea id="rulejson" rows="6">${esc(state.ruleJSON)}</textarea>
            <div class="row"><button class="pri" data-act="rules-import-do">用上面这段 JSON 覆盖当前规则</button>
            <button data-act="rules-json-clear">关闭</button></div>` : ''}
          <div class="rl">${rows.map(r => `<div class="ri${r.on ? '' : ' off'}">
            <span class="dot" data-act="rules-on" data-id="${esc(r.id)}" title="启用 / 停用" style="background:${esc(r.color)}"></span>
            <span class="nm2" data-act="rules-edit" data-id="${esc(r.id)}">${esc(r.name)}</span>
            <span class="kw">${esc(r.kw)}</span>
            <span class="op" data-act="rules-del" data-id="${esc(r.id)}">删</span></div>`).join('')
            || '<div class="un">没有匹配的规则</div>'}</div>`;
    }

    const STYLE = `
      :host{position:fixed;left:0;top:0;width:min(470px, calc(100vw - 24px));max-height:calc(100vh - 32px);z-index:2147483647;
        display:flex;flex-direction:column;overflow:hidden;background:#fff;color:#212121;border-radius:12px;
        box-shadow:0 10px 40px rgba(0,0,0,.22);font:13px/1.6 -apple-system,"Segoe UI","Microsoft YaHei",sans-serif}
      .bar{display:flex;align-items:flex-end;gap:2px;padding:8px 6px 0 8px;border-bottom:1px solid #eee;
        background:#fafafa;flex:none;cursor:move;user-select:none;touch-action:none;position:relative}
      .tabs{display:flex;flex:1;min-width:0;gap:2px;flex-wrap:wrap}
      .tab{padding:6px 9px;font-size:12px;cursor:pointer;border-radius:6px 6px 0 0;color:#666;white-space:nowrap}
      .tab.on{background:#fff;color:#fb7299;font-weight:600}
      .body{padding:12px;overflow:auto}
      .row{display:flex;gap:6px;align-items:center;margin-bottom:8px;flex-wrap:wrap}
      input,select{border:1px solid #ddd;border-radius:5px;padding:4px 7px;font:inherit;font-size:12px;background:#fff;color:#212121}
      input{width:110px}input[type=date]{width:120px}
      /* 规则筛选按钮：颜色走 --c 自定义属性，选中态填色底 + 白字 */
      .frow{display:flex;flex-wrap:wrap;gap:4px;margin-bottom:8px}
      .fb{border:1px solid var(--c,#ddd);color:#666;border-radius:10px;padding:1px 8px;font-size:12px;
        cursor:pointer;user-select:none;white-space:nowrap}
      .fb.on{background:var(--c,#909399);border-color:var(--c,#909399);color:#fff;font-weight:600}
      button{border:1px solid #fb7299;background:#fff;color:#fb7299;border-radius:5px;padding:4px 10px;font:inherit;font-size:12px;cursor:pointer}
      button.pri{background:#fb7299;color:#fff}
      button:disabled{opacity:.35;cursor:default}
      /* 翻页条钉在面板底部：body 是滚动容器，sticky bottom 让它始终在手边 */
      .pg{position:sticky;bottom:-12px;margin:8px -12px -12px;padding:8px 12px;background:#fff;
        border-top:1px solid #eee;display:flex;gap:6px;align-items:center;flex-wrap:wrap}
      .list{transition:opacity .15s}
      .list.dim{opacity:.35;pointer-events:none}
      @keyframes cfqsh{0%{background-position:200% 0}100%{background-position:-200% 0}}
      .sk{height:12px;margin:6px 0;border-radius:3px;background:linear-gradient(90deg,#f2f2f2,#e6e6e6,#f2f2f2);
        background-size:200% 100%;animation:cfqsh 1.1s linear infinite}
      h4{margin:12px 0 6px;font-size:12px;color:#666}
      .chip{display:inline-block;margin:2px 4px 2px 0;padding:2px 7px;border-radius:10px;font-size:12px;border:1px solid;cursor:default}
      .chip[data-act]{cursor:pointer}
      .why{color:#999;font-size:11px;white-space:pre-wrap;margin:1px 0 6px;padding-left:6px;border-left:2px solid #eee}
      .sup{color:#aaa;font-size:11px;margin:2px 0;padding-left:6px;border-left:2px solid #f5f5f5}
      .un{color:#aaa;font-size:12px;margin:2px 0}
      .kv{display:grid;grid-template-columns:auto 1fr auto 1fr;gap:2px 8px;font-size:12px;color:#555}
      .kv b{font-weight:400;color:#888}
      .item{display:block;border-top:1px dashed #eee;padding:5px 0;font-size:12px;color:inherit;text-decoration:none}
      .item:hover{background:#fff6f8}
      /* 命中原文直链：不使用浏览器默认的蓝色下划线样式，只保留可点击性 */
      .lk{margin:2px 0 8px;font-size:12px;line-height:1.8;color:#888}
      .lk a{color:#7a7a7a;text-decoration:none;border-bottom:1px dotted #d8d8d8;padding-bottom:1px}
      .lk a:hover{color:#fb7299;border-bottom-color:#fb7299}
      .t{color:#aaa;font-size:11px}
      .warn{background:#fff4f4;border:1px solid #ffd3d3;border-radius:6px;padding:6px 8px;font-size:12px;color:#c33;margin:8px 0}
      .hd{display:flex;align-items:center;gap:10px;margin-bottom:8px}
      .hd img{width:38px;height:38px;border-radius:50%;background:#eee;object-fit:cover}
      .nm{font-weight:600;font-size:14px;word-break:break-all}
      /* 标签栏右侧的两个控件：齿轮展开设置，× 关闭面板，两者同尺寸同基线 */
      .ctl{flex:none;width:26px;height:26px;margin-bottom:2px;display:inline-flex;align-items:center;
        justify-content:center;border-radius:6px;cursor:pointer;color:#999;user-select:none}
      .ctl:hover,.ctl.on{color:#fb7299;background:rgba(251,114,153,.08)}
      .sw{margin-left:auto;align-self:center;display:inline-flex;align-items:center;justify-content:center;height:22px;padding:0 10px;margin-right:8px;border-radius:11px;font-size:12px;line-height:1;white-space:nowrap;cursor:pointer;user-select:none;color:#bbb;background:#f4f4f4;border:1px solid #e5e5e5}
      .sw.on{color:#fb7299;background:rgba(251,114,153,.08);border-color:rgba(251,114,153,.35)}
      .sw + .sw{margin-left:0}      /* 两颗药丸挨着排，别让第二颗的 auto 外边距把它们撑开 */
      .row .sw{margin-left:0}       /* 证据通道那排药丸排在 .row 里，不要贴到右边 */
      /* 设置弹层：开关不常驻标签栏，由齿轮展开 */
      .set{position:fixed;left:0;top:0;z-index:2;background:#fff;border:1px solid #ececec;
        border-radius:9px;box-shadow:0 6px 22px rgba(0,0,0,.14);padding:7px 10px;min-width:200px;cursor:default;
        max-height:calc(100vh - 16px);overflow:auto}
      .set .si{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:3px 0;font-size:12px;color:#555}
      .set .si .sw{margin-left:0}
      .set .sn{color:#bbb;font-size:11px;margin:-2px 0 3px;text-align:right}
      .set .sg{margin:8px 0 2px;padding-top:6px;border-top:1px solid #f0f0f0;color:#999;font-size:11px;letter-spacing:.5px}
      .set .sg:first-child{margin-top:0;padding-top:0;border-top:0}
      /* 规则页 */
      textarea{width:100%;box-sizing:border-box;border:1px solid #ddd;border-radius:5px;padding:5px 7px;
        font:11px/1.5 Consolas,monospace;color:#333;margin-bottom:8px;resize:vertical}
      .rf{display:grid;grid-template-columns:1fr 1fr;gap:6px;background:#fafafa;border:1px solid #eee;
        border-radius:8px;padding:8px;margin-bottom:8px}
      .rf label{display:flex;flex-direction:column;gap:2px;font-size:11px;color:#888}
      .rf label.wide{grid-column:1/-1}
      .rf input{width:auto;box-sizing:border-box}
      .rf .rfbtn{grid-column:1/-1;margin:2px 0 0}
      .rl{display:flex;flex-direction:column;border-top:1px solid #eee}
      .ri{display:flex;align-items:center;gap:6px;padding:3px 0;border-bottom:1px dashed #f0f0f0;font-size:12px}
      .ri.off{opacity:.4}
      .ri .dot{width:10px;height:10px;border-radius:50%;flex:none;cursor:pointer;border:1px solid rgba(0,0,0,.15)}
      .ri .nm2{cursor:pointer;flex:none;min-width:74px;font-weight:600}
      .ri .kw{color:#999;font-size:11px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
      .ri .op{margin-left:auto;color:#fb7299;cursor:pointer;flex:none;font-size:11px}
    `;

    const POS_KEY = 'cfq_pos';
    let shadow = null, panelHost = null, placed = false, lastTab = '';

    // 将面板按实际尺寸约束在视口内，避免窗口尺寸变化后移出可见区域
    function clampIntoView() {
        if (!panelHost) return;
        const w = panelHost.offsetWidth || 470, h = panelHost.offsetHeight || 400;
        const num = v => Number(String(v).replace('px', '')) || 0;
        panelHost.style.left = clamp(num(panelHost.style.left), 8, Math.max(8, innerWidth - w - 8)) + 'px';
        panelHost.style.top = clamp(num(panelHost.style.top), 8, Math.max(8, innerHeight - h - 8)) + 'px';
    }

    // 设置弹层是 position:fixed 的：面板本身 overflow:hidden，绝对定位会被底边裁掉。
    // 锚在齿轮正下方，下面放不下就翻到上方，左右都夹在视口里；拖动面板时要跟着重算。
    function placeSettings() {
        if (!shadow || !state.showSettings) return;
        const set = shadow.querySelector('.set'), gear = shadow.querySelector('[data-act="gear"]');
        if (!set || !gear) return;
        const g = gear.getBoundingClientRect(), w = set.offsetWidth, h = set.offsetHeight;
        set.style.top = (innerHeight - g.bottom - 12 >= h ? g.bottom + 6 : Math.max(8, g.top - 6 - h)) + 'px';
        set.style.left = clamp(g.right - w, 8, Math.max(8, innerWidth - w - 8)) + 'px';
    }

    function placePanel() {
        const saved = GM_getValue(POS_KEY, null);
        const w = panelHost.offsetWidth || 470, h = panelHost.offsetHeight || 400;
        panelHost.style.left = (Number.isFinite(saved?.x) ? saved.x : (innerWidth - w) / 2) + 'px';
        panelHost.style.top = (Number.isFinite(saved?.y) ? saved.y : (innerHeight - h) / 2) + 'px';
        clampIntoView();
    }

    function startDrag(e) {
        const bar = e.target.closest('.bar');
        if (!bar || e.target.closest('.tab') || e.target.closest('[data-act]')) return;
        const rect = panelHost.getBoundingClientRect();
        const dx = e.clientX - rect.left, dy = e.clientY - rect.top;
        const move = ev => {
            panelHost.style.left = (ev.clientX - dx) + 'px';
            panelHost.style.top = (ev.clientY - dy) + 'px';
            clampIntoView();
            placeSettings();      // 弹层是 fixed 的，拖面板时得跟着走
        };
        const up = () => {
            window.removeEventListener('pointermove', move);
            window.removeEventListener('pointerup', up);
            GM_setValue(POS_KEY, { x: parseFloat(panelHost.style.left), y: parseFloat(panelHost.style.top) });
        };
        window.addEventListener('pointermove', move);
        window.addEventListener('pointerup', up);
        e.preventDefault();
    }

    const TABS = [['query', '成分'], ['comments', '评论'], ['dm', '弹幕'], ['aicu', '跳转'], ['rules', '规则']];
    // 查询功能关闭后仍然保留的标签页：规则表是配置项，不是查询功能
    const KEEP_WHEN_OFF = new Set(['query', 'rules']);
    // 用内联 SVG 而不是文字符号：⚙/× 在不同字体下大小与基线都不稳定，和标签文字对不齐
    // 齿轮路径取自 Feather Icons（MIT，© Cole Bemis，https://github.com/feathericons/feather）的 settings 图标
    const ICON_GEAR = '<svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/></svg>';
    const ICON_X = '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"><path d="M18 6 6 18M6 6l12 12"/></svg>';

    function render() {
        if (!shadow) {
            panelHost = document.createElement('div');
            panelHost.className = 'cfq3-host';
            document.body.appendChild(panelHost);
            shadow = panelHost.attachShadow({ mode: 'open' });
            shadow.addEventListener('click', onShadowClick);
            shadow.addEventListener('change', onShadowChange);
            shadow.addEventListener('pointerdown', startDrag);
            shadow.addEventListener('keydown', e => {
                if (e.key !== 'Enter') return;
                if (e.target.id === 'uid-comments') { syncTab(); loadComments(1); }
                else if (e.target.id === 'uid-dm') { syncTab('dm'); loadDanmu(1); }
                else if (e.target.id === 'mid') runQuery(e.target.value.trim());
            });
            addEventListener('resize', clampIntoView);
        }
        const body = state.tab === 'comments' ? tabComments()
            : state.tab === 'dm' ? tabDanmu()
            : state.tab === 'aicu' ? tabAicu()
            : state.tab === 'rules' ? tabRules() : tabQuery();
        // innerHTML 整体重建会将滚动容器重置到顶部，
        // 因此在同一标签页内保留滚动位置，切换标签页或重开面板时才回到顶部。
        const keepScroll = state.tab === lastTab ? (shadow.querySelector('.body')?.scrollTop || 0) : 0;
        lastTab = state.tab;
        const tabs = state.queryOn ? TABS : TABS.filter(([k]) => KEEP_WHEN_OFF.has(k));
        shadow.innerHTML = `<style>${STYLE}</style>
          <div class="bar"><div class="tabs">${tabs.map(([k, n]) => `<div class="tab ${state.tab === k ? 'on' : ''}" data-tab="${k}">${n}</div>`).join('')}</div>
            <span class="ctl${state.showSettings ? ' on' : ''}" data-act="gear" title="设置">${ICON_GEAR}</span>
            <span class="ctl" data-act="close" title="关闭">${ICON_X}</span>
            ${state.showSettings ? settingsPop() : ''}</div>
          <div class="body">${state.tabError ? `<div class="warn">操作出错：${esc(state.tabError)}</div>` : ''}${body}</div>`;
        const bodyEl = shadow.querySelector('.body');
        if (bodyEl) bodyEl.scrollTop = keepScroll;
        // 仅首次渲染时定位/居中，避免数据分步到达导致面板位移
        if (!placed) { placePanel(); placed = true; }
        else clampIntoView();      // 内容变高时把面板拉回屏内，不让它长到屏幕外
        placeSettings();           // 面板刚量完尺寸，弹层的 fixed 坐标要按新位置重算
    }

    function closePanel() {
        panelHost?.remove();
        panelHost = null;
        shadow = null;
        placed = false;
        lastTab = '';      // 下次打开从顶部开始，不恢复上次的滚动位置
    }

    /* ══════════════ 面板事件：输入框同步 / 点击派发 ══════════════ */

    // 将 UID 输入框当前值同步回 state，并切换到该 UID 对应的分页桶
    function syncTab(which = 'comments') {
        const v = shadow.querySelector(which === 'dm' ? '#uid-dm' : '#uid-comments')?.value?.trim();
        if (v && v !== state[which].uid) bucketUse(v, state[which].src, which);
    }

    function onShadowChange(e) {
        const rf = e.target.dataset?.rf;
        if (rf) {
            const r = state.rules.find(x => x.id === e.target.dataset.id);
            if (r) {
                let v = e.target.value.trim();
                if (rf === 'color') { if (!v) v = '#ff6699'; if (v[0] !== '#') v = '#' + v; }
                if (rf === 'name' && !v) return render();      // 显示名留空等于把这条规则藏起来，不给写
                r[rf] = v;
                saveRules();
            }
            return render();
        }
        if (e.target.id === 'ruleq') { state.ruleQ = e.target.value; return render(); }
        if (e.target.id === 'src') {
            // 切换数据源即切换缓存桶，避免沿用上一数据源的结果
            const src = e.target.value, uid = state.comments.uid;
            bucketUse(uid, src);
            state.filter = '';
            return render();
        }
        if (e.target.id === 'dm-src') {
            const src = e.target.value, uid = state.dm.uid || state.mid;
            bucketUse(uid, src, 'dm');
            state.filter = '';
            return render();
        }
    }

    async function onShadowClick(e) {
        try { await handleShadowClick(e); }
        catch (err) {
            // 不静默吞掉异常：否则界面仅表现为按钮无响应
            state.tabError = String(err?.message || err);
            render();
        }
    }

    async function handleShadowClick(e) {
        state.tabError = null;
        const tab = e.target.closest('.tab');
        if (tab) { state.tab = tab.dataset.tab; return render(); }
        // 图标用内联 SVG 时命中节点是 <path>，因此向上找带 data-act 的元素
        const actEl = e.target.closest('[data-act]');
        const act = actEl?.dataset?.act;
        if (!act) return;
        if (act === 'filter-set') { state.filter = actEl.dataset.id || ''; return render(); }
        if (act === 'close') return closePanel();
        if (act === 'relay-toggle') {
            state.relay = !state.relay;
            GM_setValue('cfq_relay', state.relay);
            return render();
        }
        if (act === 'gear') { state.showSettings = !state.showSettings; return render(); }
        if (act === 'set-query') {
            state.queryOn = !state.queryOn;
            GM_setValue('cfq_query', state.queryOn);
            // 关闭查询功能时不停留在已隐藏的标签页
            if (!state.queryOn && !KEEP_WHEN_OFF.has(state.tab)) state.tab = 'query';
            return render();
        }
        if (act === 'auto-toggle') {
            state.auto = !state.auto;
            GM_setValue('cfq_auto', state.auto);
            if (state.auto) scan(); else clearFloorTags();
            return render();
        }
        if (act === 'live-toggle') {
            state.liveTags = !state.liveTags;
            GM_setValue('cfq_live', state.liveTags);
            if (state.liveTags) scanLive(); else clearLiveButtons();
            return render();
        }
        if (act === 'dm-list-toggle') {
            state.dmList = !state.dmList;
            GM_setValue('cfq_dm_list', state.dmList);
            if (state.dmList) hookDmList(); else unhookDmList();
            return render();
        }
        if (act === 'dm-verify-toggle') {
            state.dmVerify = !state.dmVerify;
            GM_setValue('cfq_dm_verify', state.dmVerify);
            return render();
        }
        if (act === 'dm-deep-toggle') {
            state.dmDeep = !state.dmDeep;
            GM_setValue('cfq_dm_deep', state.dmDeep);
            return render();
        }
        if (act === 'query') return runQuery(shadow.querySelector('#mid')?.value.trim());
        if (act === 'videos') {
            state.vidMore = 10;
            state.videos = await API.videos(state.mid);
            return render();
        }
        if (act === 'videos-more') { state.vidMore += 20; return render(); }
        if (act === 'go-comments') {
            syncTab();
            const t = state.comments;
            t.pn = 1; t.cursors = ['']; t.rows = []; t.total = null; t.end = false;
            state.filter = '';
            return loadComments(1);
        }
        if (act === 'pg-comments') {
            syncTab();
            // 换页后「本页命中的规则」集合随之变化，需清除失效筛选，避免出现「列表无该项但仍在筛选」
            state.filter = '';
            return loadComments(clamp(Number(actEl.dataset.pn) || 1, 1, 9999));
        }
        if (act === 'pg-comments-jump') {
            syncTab();
            const pn = clamp(Number(shadow.querySelector('#jumppn')?.value) || 1, 1, 9999);
            state.filter = '';
            return loadComments(pn);
        }
        if (act === 'go-dm') {
            syncTab('dm');
            const t = state.dm;
            t.pn = 1; t.rows = []; t.total = null; t.end = false;
            state.filter = '';
            return loadDanmu(1);
        }
        if (act === 'pg-dm' || act === 'pg-dm-jump') {
            syncTab('dm');
            state.filter = '';
            const pn = act === 'pg-dm'
                ? clamp(Number(actEl.dataset.pn) || 1, 1, 9999)
                : clamp(Number(shadow.querySelector('#jumppn')?.value) || 1, 1, 9999);
            return loadDanmu(pn);
        }
        /* ── 规则页与证据通道开关 ── */
        const EV_KEY = { evMedal: 'cfq_ev_medal', evFollow: 'cfq_ev_follow', evDynPages: 'cfq_ev_dyn' };
        if (act === 'rules-new') {
            const r = normRule({ n: '新成分', k: '', c: '#ff6699' });
            r.kw = '';                       // 不以显示名作为默认关键词，避免新建规则立即产生误命中
            state.rules.unshift(r);          // 新增条目置顶，便于立即定位
            saveRules();
            state.ruleEdit = r.id; state.ruleNewId = r.id; state.ruleMore = false; state.ruleQ = '';
            return render();
        }
        if (act === 'rules-cancel') {
            // 仅回滚本次新建的那条；已有字段的修改是即时落盘的，不存在可回滚的草稿
            if (state.ruleNewId) {
                state.rules = state.rules.filter(r => r.id !== state.ruleNewId);
                saveRules();
            }
            state.ruleEdit = ''; state.ruleNewId = '';
            return render();
        }
        if (act === 'rules-more') { state.ruleMore = !state.ruleMore; return render(); }
        if (act === 'rules-edit') { state.ruleEdit = actEl.dataset.id; state.ruleNewId = ''; return render(); }
        if (act === 'rules-close') { state.ruleEdit = ''; state.ruleNewId = ''; state.ruleMore = false; return render(); }
        if (act === 'rules-on') {
            const r = state.rules.find(x => x.id === actEl.dataset.id);
            if (r) { r.on = !r.on; saveRules(); }
            return render();
        }
        if (act === 'rules-del') {
            const id = actEl.dataset.id;
            state.rules = state.rules.filter(r => r.id !== id);
            // 内置规则需记入 deleted，否则下次加载会被合并回来，删除不生效
            if (DEFAULT_RULES.some(d => d.id === id)) state.rulesDeleted = [...new Set([...(state.rulesDeleted || []), id])];
            if (state.ruleEdit === id) state.ruleEdit = '';
            saveRules();
            return render();
        }
        if (act === 'rules-reset') { state.ruleResetAsk = true; return render(); }
        if (act === 'rules-reset-yes') {
            GM_setValue(RULES_KEY, { ver: 1, rules: [], deleted: [] });
            state.rulesDeleted = [];
            loadRules();
            tagCache.clear(); floorMem.clear();
            state.ruleEdit = ''; state.ruleJSON = ''; state.ruleResetAsk = false;
            state.ruleNewId = ''; state.ruleMore = false;
            return render();
        }
        if (act === 'rules-export') { state.ruleJSON = JSON.stringify(state.rules.map(toRow), null, 1); state.ruleEdit = ''; return render(); }
        if (act === 'rules-import') { state.ruleJSON = state.ruleJSON || '[\n  {"id":"my1","g":"分组","n":"显示名","k":"关键词1|关键词2","c":"#ff6699","m":"","o":""}\n]'; state.ruleEdit = ''; return render(); }
        if (act === 'rules-json-clear') { state.ruleJSON = ''; return render(); }
        if (act === 'rules-import-do') {
            let parsed;
            try { parsed = JSON.parse(shadow.querySelector('#rulejson')?.value || ''); }
            catch (err) { state.tabError = 'JSON 解析失败：' + err.message; return render(); }
            if (!Array.isArray(parsed) || !parsed.length) { state.tabError = '要的是一个非空的规则数组'; return render(); }
            const rows = parsed.map(p => normRule({
                id: p.id, g: p.g ?? p.group, n: p.n ?? p.name, k: p.k ?? p.kw,
                c: p.c ?? p.color, m: p.m ?? p.medal, o: p.o ?? p.off, on: p.on,
            }));
            const bad = rows.find(r => !r.name || r.name === '未命名');
            if (bad) { state.tabError = '有一条缺显示名（n / name 字段）'; return render(); }
            state.rules = rows;
            state.rulesDeleted = [];
            state.ruleJSON = ''; state.ruleEdit = '';
            saveRules();
            return render();
        }
        if (act === 'ev-goto') {
            const m = actEl.dataset.mid;
            if (m) runQuery(m);
            return;
        }
        if (act.startsWith('ev-')) {
            const k = act.slice(3);
            if (!EV_KEY[k]) return;
            state[k] = !state[k];
            GM_setValue(EV_KEY[k], state[k]);
            // 面板已打开某个用户时，切换通道后立即重取证据
            const m = state.query?.mid;
            if (m) {
                state.query.ev = null;
                fetchEvidence(m).then(r => {
                    if (state.query?.mid === m) { state.query.ev = r; render(); }
                }).catch(err => {
                    if (state.query?.mid === m) { state.query.ev = evFail(err); render(); }
                });
            }
            return render();
        }
        if (act === 'aicu-set') {
            const v = shadow.querySelector('#uid-aicu')?.value?.trim();
            if (v) bucketUse(v);
            return render();
        }
        if (act === 'aicu') {
            const uid = state.comments.uid || state.mid;
            if (!/^\d+$/.test(String(uid))) { state.tabError = '先给一个数字 UID（可在「成分」输用户名，它会自动解析）'; return render(); }
            window.open(`https://www.aicu.cc${actEl.dataset.p}?uid=${encodeURIComponent(uid)}`, '_blank', 'noopener');
            return;
        }
    }

    /* ══════════════ 楼层图标 ══════════════ */

    const ICON = '<svg viewBox="0 0 1024 1024" width="12" height="12" aria-hidden="true" style="vertical-align:-2px"><path fill="currentColor" d="M448 128a320 320 0 0 1 250.6 519.7l178.2 178.2a42.7 42.7 0 0 1-60.4 60.4L638.2 708.1A320 320 0 1 1 448 128zm0 85.3a234.7 234.7 0 1 0 0 469.4 234.7 234.7 0 0 0 0-469.4z"/></svg>';

    // 不右浮动到行尾：#header 右端为 B站的 ornament（铭牌/头像框）卡片，浮动会重叠
    // margin-right 是给选中态那圈描边留的位：描边贴在按钮外沿，昵称容器 overflow:hidden
    // 不留位就会被切掉一角。留成常态而不是点中时才加，免得点一下把后面的文字顶得跳
    const FLOOR_STYLE = 'display:inline-flex;align-items:center;vertical-align:middle;' +
        'margin:0 2px 0 8px;padding:2px 6px;border-radius:4px;cursor:pointer;color:#fb7299;' +
        'background:rgba(251,114,153,.08);border:1px solid rgba(251,114,153,.3);user-select:none;';

    // 点一下动一下：让「这一下收到了」看得见。楼层/直播/弹幕三处共用，走 WAAPI 不往页面塞样式表
    const cfqPulse = (el, base = '') => el.animate(
        [{ transform: base + 'scale(1)' }, { transform: base + 'scale(1.6)' }, { transform: base + 'scale(1)' }],
        { duration: 260 });
    // 当前查询对象描个边，免得在一屏楼层里找刚点的是哪个。只记一个节点引用：
    // 评论区楼层在影子根里，document 查不到，描边/摘边都只能攥着节点本身。
    let cfqActiveBtn = null;
    function markActive(el) {
        if (cfqActiveBtn && cfqActiveBtn !== el) cfqActiveBtn.style.outline = 'none';
        cfqActiveBtn = el || null;
        if (cfqActiveBtn) cfqActiveBtn.style.outline = '1px solid #fb7299';
    }

    function floorButton(uid, extraStyle) {
        const b = document.createElement('span');
        b.className = 'cfq3-floor';
        b.innerHTML = ICON;
        b.style.cssText = FLOOR_STYLE + (extraStyle || '');
        b.title = '查成分';
        b.dataset.cfqUid = uid;                       // 记着这颗按钮绑的是谁，行被复用时要拿它比对
        b.addEventListener('click', e => {
            e.preventDefault(); e.stopPropagation();
            runQuery(uid);        // runQuery 会先清掉上一个描边，所以标记要放在它后面
            markActive(b);
        });
        return b;
    }

    function mountFloorButton(container, uid) {
        if (!container || !uid) return;
        const old = container.querySelector('.cfq3-floor');
        if (old) { if (old.dataset.cfqUid === String(uid)) return; old.remove(); }   // 容器被换成别人：重挂，别查错人
        container.appendChild(floorButton(uid));
    }

    /* ══════════════ 楼层自动挂标签 ══════════════
     * 语料只用其空间动态 data（面板侧另计昵称与签名）；无命中挂默认标签，接口失败挂 errorTag，
     */
    const BLOG_API = 'https://api.bilibili.com/x/polymer/web-dynamic/v1/feed/space?&host_mid=';
    function dynRaw(uid, offset) {
        return new Promise(resolve => GM_xmlhttpRequest({
            method: 'GET', url: BLOG_API + uid + (offset ? '&offset=' + encodeURIComponent(offset) : ''), timeout: 5000,
            onload: res => {
                if (res.status !== 200) return resolve({ fail: 'HTTP ' + res.status });
                let j;
                try { j = JSON.parse(res.responseText ?? res.response); }
                catch (e) { return resolve({ fail: '响应非 JSON（验证页/滑块页）' }); }
                if (!j?.data) return resolve({ fail: 'code=' + j?.code });
                resolve({ data: j.data });
            },
            onerror: () => resolve({ fail: '网络错误' }),
            ontimeout: () => resolve({ fail: '超时' }),
        }));
    }

    const floorMem = new Map(), floorPending = new Set(), floorContainers = new Set();
    const floorWaiters = new Map();   // uid -> 等待同一份结果的其他楼层

    /* ── 楼层流程的两个上限，都是天花板不是配额 ──
     * 视口裁剪：屏幕外不发请求（滚到位由下一次 schedule 补）；在飞上限：只在狂滚且请求长时间不返回时触及。
     * 首屏 20 人仍是一轮全发，与加闸门之前一致。 */

    const floorGateQ = [];
    let floorInflight = 0;
    async function floorSlot() {
        if (floorInflight >= CFG.floorInflight) await new Promise(r => floorGateQ.push(r));
        floorInflight++;
    }
    function floorRelease() {
        floorInflight--;
        const next = floorGateQ.shift();
        if (next) next();
    }
    const inView = el => {
        const r = el.getBoundingClientRect();
        return r.bottom > -CFG.floorMargin && r.top < innerHeight + CFG.floorMargin;
    };

    function tagSpan(t, uid) {
        const span = document.createElement('span');
        span.className = 'cfq3-tag';
        span.textContent = t.name;
        span.style.cssText = 'display:inline-flex;align-items:center;margin-left:6px;' +
            'font-size:11px;line-height:14px;padding:1px 4px;border-radius:3px;' +
            'background:rgba(0,0,0,0.04);color:' + t.color + ';border:1px solid ' + withAlpha(t.color) + ';' +
            'white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:150px;' +
            'user-select:none;flex-shrink:0;vertical-align:middle;cursor:pointer;';
        span.title = ((t.tip || t.name) + '\n点标签打开面板看完整归因').slice(0, 900);
        span.addEventListener('click', e => { e.preventDefault(); e.stopPropagation(); runQuery(uid); });
        return span;
    }

    function renderFloorTags(container, uid, tags) {
        // 键名用 cfqUid 而非 uid：避免与同类脚本的记账键冲突，导致双方都误判为已挂载
        container.dataset.cfqUid = String(uid);
        container.querySelectorAll('.cfq3-tag').forEach(el => el.remove());
        const anchor = container.querySelector('.cfq3-floor');   // 标签排在查询图标左侧
        for (const t of tags) container.insertBefore(tagSpan(t, uid), anchor || null);
        if (!floorContainers.has(container)) {
            floorContainers.add(container);
            // 集合只增不减会持住已销毁楼层的整棵 shadow 树：超出上限时剔除断开的那些
            if (floorContainers.size > CFG.floorContainersMax)
                for (const c of floorContainers) if (!c.isConnected) floorContainers.delete(c);
        }
    }

    const floorTagsOf = raws => analyze(collectCorpus(raws)).tags;

    function autoTag(uid, container) {
        if (!state.auto || !uid || !container) return;
        const k = String(uid);
        if (container.querySelector('.my-tag')) return;                                  // 同类脚本已挂载则不重复
        if (container.dataset.cfqUid === k && container.querySelector('.cfq3-tag')) return; // 已挂载且属于同一用户
        const known = floorMem.get(k) || tagCache.get(k);
        if (known) { floorMem.set(k, known); return renderFloorTags(container, uid, known); }
        if (!inView(container)) return;                                                    // 视口外不发起请求
        if (floorPending.has(k)) {
            // 同一用户可出现在多个楼层（主评论 + 楼中楼）：请求进行中时登记楼层，返回后一并渲染
            const w = floorWaiters.get(k) || [];
            if (!w.includes(container)) w.push(container);
            floorWaiters.set(k, w);
            return;
        }
        floorPending.add(k);
        const paint = c => {
            if (c.isConnected && (!c.dataset.cfqUid || c.dataset.cfqUid === k)) renderFloorTags(c, uid, slim);
        };
        let slim;
        (async () => {
            await floorSlot();
            try {
                // 先走免签名的裸请求（不排队、并发），失败才退回验签慢路
                const raw = await fetchDyn1(k);
                if (raw.fail) throw new Error(raw.fail);
                // 同时预热按人缓存，点开面板时无需重复请求动态
                personCache.patch(k, { raws: [raw.data] });
                const tags = floorTagsOf([raw.data]);
                // 落盘的那份去掉原文片段，只保留标签名/颜色/来源统计
                slim = tags.map(t => ({
                    name: t.name, color: t.color, ruleKey: t.ruleKey,
                    tip: (t.why || '').split('\n').filter(l => !l.includes('“')).join('\n'),
                }));
            } catch (e) {
                slim = [{ name: ERROR_TAG.name, color: ERROR_TAG.color, tip: String((e && e.message) || e) }];
            } finally {
                floorRelease();
            }
            floorMem.set(k, slim); tagCache.set(k, slim);
            paint(container);
            (floorWaiters.get(k) || []).forEach(paint);
            floorPending.delete(k); floorWaiters.delete(k);
        })();
    }

    function clearFloorTags() {
        for (const c of floorContainers) {
            if (!c.isConnected) { floorContainers.delete(c); continue; }
            c.querySelectorAll('.cfq3-tag').forEach(el => el.remove());
        }
    }

    const commentRoot = () => document.querySelector('bili-comments')?.shadowRoot || null;
    let mainObserver = null, observedRoot = null, queued = false;
    const seenThread = new WeakSet(), seenReplies = new WeakSet();

    function schedule() {
        if (queued) return;
        queued = true;
        setTimeout(() => { queued = false; scan(); }, 150);
    }
    const observeShadow = el => { if (el?.shadowRoot) new MutationObserver(schedule).observe(el.shadowRoot, { childList: true, subtree: true }); };

    /* 兜底穿隧：若 B站日后在 renderer 与 #header 之间再包一层 shadow，固定深链会
     * 静默失效（无报错，仅标签全部消失）。
     * 仅在固定选择器无结果时执行，且带节点预算与首个命中即停，不会退化为全页扫描。 */
    function qDeep(root, sel, budget = 2000, depth = 0, out = []) {
        if (!root || depth > 8 || out.length) return out;
        const kids = root.children || root.childNodes || [];
        for (const el of kids) {
            if (out.length || --budget <= 0) return out;
            if (el.nodeType !== 1) continue;
            if (el.matches?.(sel)) out.push(el);
            else if (el.shadowRoot) qDeep(el.shadowRoot, sel, budget, depth + 1, out);
        }
        return out;
    }

    // UID 的两个已知落点及深链失败时的兜底；取不到返回空，不做推测
    function uidOf(renderer) {
        const sr = renderer?.shadowRoot;
        return sr?.querySelector('#user-avatar')?.dataset.userProfileId
            || sr?.querySelector('#user-name')?.dataset.userProfileId
            || qDeep(renderer, '[data-user-profile-id]')[0]?.dataset?.userProfileId || '';
    }
    function headerOf(renderer) {
        const sr = renderer?.shadowRoot;
        return sr?.querySelector('#header') || qDeep(renderer, '#header')[0] || null;
    }

    /* ══════════════ 扫描：Shadow DOM 穿透 + 逐层挂图标/挂标签 ══════════════
     * 评论区在 bili-comments 的 shadowRoot 内，楼层又在 bili-comment-renderer 的下一层 shadowRoot，需逐层穿透；
     */

    /* ── 直播间弹幕栏：昵称旁挂同一个查询按钮 ──
     * #chat-items > div.chat-item.danmaku-item，无 shadow DOM；UID 在行 data-uid，昵称在 .common-nickname-wrapper。
     * 行只追加不回收（实测 9s 内 109→157 且 uid 不复用），故按行 dataset 记账即可。
     */
    const LIVE_STYLE = 'margin-left:4px;margin-right:2px;padding:0 5px;';
    const LIVE_CAP = 40;      // 单轮最多挂载的行数：进入房间时列表已有数百条，分摊到数轮完成
    let liveRoot = null, liveObserver = null;

    function scanLive() {
        const list = document.getElementById('chat-items');
        if (!list) {
            if (liveObserver) { liveObserver.disconnect(); liveObserver = null; liveRoot = null; }
            return;
        }
        if (!state.liveTags) return;      // 关闭时不再挂载；已挂载的由开关回调清除
        if (list !== liveRoot) {
            liveObserver?.disconnect();
            liveObserver = new MutationObserver(schedule);
            liveObserver.observe(list, { childList: true });
            liveRoot = list;
        }
        const todo = [];
        // 从尾部向前遍历：新行追加在底部，优先挂载可视区域内的行，其余排入后续轮次
        for (let i = list.children.length - 1; i >= 0 && todo.length < LIVE_CAP; i--) {
            const row = list.children[i];
            if (row?.nodeType !== 1 || !row.classList.contains('danmaku-item')) continue;
            // 登记里存的是「这行当时是谁」而不是一个 1：直播弹幕行会被回收复用，
            // 只认「挂过就不再管」会让按钮停在旧 UID 上，点出来的是别人的成分
            const cur = row.dataset.uid || '0';
            if (row.dataset.cfqLive === cur) continue;
            row.dataset.cfqLive = cur;             // 先行登记：本轮无法挂载的匿名行无需下一轮再遍历
            todo.push(row);
        }
        for (const row of todo) {
            const uid = row.dataset.uid || '0';
            if (uid === '0' || !/^\d+$/.test(uid)) { row.dataset.cfqLive = uid; continue; }   // 匿名发言/系统消息：本来就不挂，登记掉免得反复遍历
            const wrap = row.querySelector('.common-nickname-wrapper') || row.querySelector('.user-name')?.parentElement;
            if (!wrap) continue;                                  // 昵称节点还没渲染出来：不登记，下一轮再试
            if (wrap.dataset.cfqUid !== uid) {                    // 换人了：先摘掉上一位的按钮再挂新的
                wrap.querySelector('.cfq3-floor')?.remove();
                wrap.dataset.cfqUid = uid;
                wrap.appendChild(floorButton(uid, LIVE_STYLE));
            }
            row.dataset.cfqLive = uid;
        }
    }

    // 关掉开关时撤掉已挂的按钮，并清掉行上的登记，重新打开后能再挂一遍
    function clearLiveButtons() {
        const list = document.getElementById('chat-items');
        if (!list) return;
        for (const row of list.children) {
            if (row?.nodeType !== 1) continue;
            row.querySelectorAll('.cfq3-floor').forEach(b => b.remove());
            // 昵称框上的「挂给谁」也要一起清掉，否则重新打开时会被判定成「还是那个人」而不再挂
            row.querySelectorAll('[data-cfq-uid]').forEach(w => delete w.dataset.cfqUid);
            if (row.dataset) delete row.dataset.cfqLive;
        }
    }

    /* ══════════════ 播放器弹幕列表：就地反查发送者 ══════════════
     * B站 只在 seg.so 的 protobuf 里给 midHash（字段 6），没有 UID 字段；midHash 就是 UID 十进制串的
     * CRC32（无盐），所以本地建 10 万条彩虹表即可爆破回来，不必引第三方数据源。
     * 面板行本身既无 midHash 也拿不到播放器闭包，因此必须自己拉该段再按「整秒 + 文本」对齐：
     * 面板显示的秒数是向下取整，用 round 会漏掉一半；分段实测 6 分钟一段，越界段回 304 空体。
     * 段内含弹幕正文，只进内存；持久化的只有 midHash→UID 这一层无正文的映射。
     */
    const W = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;
    const CRC_T = new Uint32Array(256);
    for (let i = 0; i < 256; i++) { let c = i; for (let j = 0; j < 8; j++) c = (c & 1) ? (c >>> 1) ^ 0xEDB88320 : c >>> 1; CRC_T[i] = c; }
    const crcUp = (crc, b) => ((crc >>> 8) ^ CRC_T[(crc ^ b) & 255]) >>> 0;
    const crcDigits = n => { let c = 0; for (const d of String(n)) c = crcUp(c, Number(d)); return c >>> 0; };
    const crcPad5 = c => { for (let i = 0; i < 5; i++) c = crcUp(c, 0); return c >>> 0; };   // 前缀变体：位数差 5 以内靠补零对齐

    /* 彩虹表约 1.1 MB TypedArray，只在第一次真要爆破时建，启动路径不碰。
     * pad 是「前缀表」：N 位数 = 前缀 × 10 万 + 后缀，所以试到 9 位只需 1 万格前缀，
     * 试到 10 位就要 10 万格（多约 400 KB，建表实测 12ms）。 */
    let DM_RAIN = null;
    const dmRainbow = (padN = 1e4) => {
        if (DM_RAIN && DM_RAIN.pad.length >= padN) return DM_RAIN;
        // h>>>16 最大是 65535，所以 65537 格里最后一格是末桶的右边界哨兵
        const N = 1e5, pad = new Uint32Array(padN), start = new Uint32Array(65537), slot = new Uint32Array(N * 2);
        for (let i = 0; i < N; i++) start[crcDigits(i) >>> 16]++;
        for (let i = 1; i < 65537; i++) start[i] += start[i - 1];
        // 原地递减填充：结束后 start[s] 正好变成桶 s 的起点，start[s + 1] 是终点
        for (let i = 0; i < N; i++) { const h = crcDigits(i), at = --start[h >>> 16]; slot[at * 2] = h; slot[at * 2 + 1] = i; }
        for (let i = 0; i < padN; i++) pad[i] = crcPad5(crcDigits(i));
        return (DM_RAIN = { pad, slot, start });
    };
    const dmBucket = h => {
        const R = dmRainbow(), s = (h >>> 0) >>> 16, out = [];
        for (let i = R.start[s], e = R.start[s + 1] | 0; i < e; i++) if (R.slot[i * 2] === (h >>> 0)) out.push(R.slot[i * 2 + 1]);
        return out;
    };
    // 逐个位数试：len 位串等价于 0xFFFFFFFF 先吃 len 个 '0' 再吃各位数字值
    const dmCrack = (hex, maxLen = 9) => {
        const R = dmRainbow(maxLen > 9 ? 1e5 : 1e4), target = (~Number('0x' + hex)) >>> 0, out = [];
        let prefix = 4294967295;
        for (let len = 1; len <= maxLen; len++) {
            prefix = crcUp(prefix, 48);
            if (len < 6) out.push(...dmBucket((target ^ prefix) >>> 0));
            else { const lo = 10 ** (len - 6), hi = Math.min(10 ** (len - 5), R.pad.length); for (let p = lo; p < hi; p++) for (const tail of dmBucket((target ^ prefix ^ R.pad[p]) >>> 0)) out.push(p * 1e5 + tail); }
        }
        return out;
    };

    const UTF8 = new TextDecoder();
    // 只认 DmSegMobileReply.elems(顶层 1)，元素内取 2=progress(毫秒) 6=midHash 7=content，其余整段跳过
    function decodeSeg(buf) {
        const u = new Uint8Array(buf), out = [];
        let p = 0;
        const vi = () => { let s = 0, r = 0, b; do { b = u[p++]; r += (b & 127) * 2 ** (7 * s); s++; } while (b & 128 && s < 10); return r; };
        while (p < u.length && out.length < CFG.dmSegEntriesMax) {
            if ((vi() >>> 3) !== 1) break;
            const len = vi(), stop = p + len;             // 先取长度再算边界：写成 p + vi() 会先读旧 p，整段偏一字节
            const e = { sec: -1, hash: '', text: '' };
            while (p < stop) {
                const k = vi(), fn = k >>> 3, wt = k & 7;
                if (wt === 0) { if (fn === 2) e.sec = Math.floor(vi() / 1000); else vi(); }
                else if (wt === 2) { const l = vi(); const raw = u.subarray(p, p + l); p += l; if (fn === 6) e.hash = UTF8.decode(raw); else if (fn === 7) e.text = UTF8.decode(raw); }
                else if (wt === 5) p += 4; else if (wt === 1) p += 8; else { p = stop; break; }
            }
            p = stop;
            if (e.hash && e.sec >= 0) out.push(e);      // 高级/字幕弹幕常缺 progress，无法与面板行对齐
        }
        return out;
    }

    const videoCid = () => Number((W.player?.getManifest?.() || {}).cid || (W.__INITIAL_STATE__ || {}).cid || 0);

    /* 候选验真（acg 助手同款思路）：CRC32 只有 32 位，同哈希解出的 2~6 个候选里多数是没人注册的号，
     * 所以并行打名片，存在的排前面、0 级的降后（acg 直接丢弃 0 级，我们只降序以免误杀真发了弹幕的新号）。
     * 一个都不存在时返回空：这恰恰说明号主是 10 位以上的新号，此时必须说「查不到」，不能把假号端出去。 */
    async function rankUids(uids) {
        const pro = await Promise.all(uids.map(async uid => {
            const d = await getNow(`https://api.bilibili.com/x/web-interface/card?mid=${uid}`);
            const card = d.json?.code === 0 ? d.json.data?.card : null;
            return { uid, live: !!card, lv: Number(card?.level_info?.current_level || 0) };
        }));
        return pro.filter(p => p.live).sort((a, b) => (b.lv > 0) - (a.lv > 0) || a.uid - b.uid).map(p => p.uid);
    }

    async function dmSenderOf(sec, text) {
        const cid = videoCid();
        if (!cid) return { fail: '取不到当前分P 的 cid' };
        const seg = Math.floor(sec * 1000 / CFG.dmSegMs) + 1;
        const key = `${lineTag()}:seg:${cid}:${seg}`;
        let rows = dmSegCache.get(key);
        if (!rows) {
            const r = await get(`https://api.bilibili.com/x/v2/dm/web/seg.so?type=1&oid=${cid}&segment_index=${seg}`,
                { referer: location.href.split('?')[0], binary: true, timeout: 15000 });
            if (r.fail) return { fail: r.fail };
            rows = decodeSeg(r.bin);
            dmSegCache.set(key, rows);
        }
        if (!rows.length) return { fail: '这一段没有弹幕' };
        let hit = rows.filter(x => x.sec === sec && x.text === text);
        if (!hit.length) hit = rows.filter(x => Math.abs(x.sec - sec) <= 1 && x.text === text);
        if (!hit.length) return { fail: '这条弹幕不在该分段里（特殊/字幕弹幕）' };
        const maxLen = state.dmDeep ? 10 : 9;
        const uids = [];
        for (const x of hit) {
            const direct = /^b(\d+)$/.exec(x.hash);
            // 缓存键带位数：否则开过精查再关掉，会读到旧的 9 位候选表
            const ck = maxLen + ':' + x.hash;
            const got = direct ? [Number(direct[1])]
                : (/^[0-9a-fA-F]{1,8}$/.test(x.hash) ? (dmUidCache.get(ck) || dmCrack(x.hash, maxLen)) : []);
            if (got.length && !direct) dmUidCache.set(ck, got);
            uids.push(...got);
        }
        const list = [...new Set(uids)];      // 同一人发过两条会给出同一批候选，去重后再排
        if (!list.length) return { fail: '这条解不出 UID：多半号主是 10 位以上的新号，本地表覆盖不到' + (state.dmDeep ? '' : '；设置里打开「多认 10 位新号」可多覆盖一批') };
        if (!state.dmVerify || list.length < 2) return { uids: list };
        const alive = await rankUids(list);
        return alive.length ? { uids: alive }
            : { fail: `反解出的 ${list.length} 个候选名片上都查不到人，真号多半是 10 位以上的新号` };
    }

    /* 行节点被虚拟化回收，所以监听挂在容器上、全页只留一个按钮节点跟着鼠标搬。
     * 状态不能存在按钮上（一搬走这次点击的结果就作废，手抖即丢），改存 WeakMap：按行记，行被回收自动释放。 */
    let dmPanel = null, dmBtn = null, dmSpin = null, dmSpinning = false;
    const dmState = new WeakMap();
    const dmBadge = () => dmBtn.lastChild;                  // 建按钮时追加的 <i>：图标右上角的小角标
    // 角标就是「按了有没有反应」的可见答案：… 在跑，! 失败，数字 = 当前是第几个候选（单候选没得切，不显示）
    function dmPaint(row) {
        if (!dmBtn || dmBtn.parentElement !== row) return;
        const s = dmState.get(row), n = s?.uids?.length || 0;
        dmBadge().textContent = s?.busy ? '…' : s?.fail ? '!' : n > 1 ? String(s.i + 1) : '';
        dmBtn.title = s?.busy ? '正在解析，稍等' : s?.fail ||
            (n ? (n > 1 ? `候选 ${s.i + 1}/${n}：UID ${s.uids[s.i]}，再点切换` : `UID ${s.uids[0]}`) : '查这条弹幕的发送者成分');
        dmSetSpin(!!s?.busy);                               // 呼吸态跟着「当前显示的那一行」走，不跟着请求走
    }
    // 加载动效走 WAAPI：不往播放器里塞样式表，cancel() 后不留任何内联残留
    function dmSetSpin(on) {
        if (on === dmSpinning || !dmBtn) return;
        dmSpinning = on;
        dmSpin?.cancel(); dmSpin = null;
        if (on) dmSpin = dmBtn.animate([{ opacity: .25 }, { opacity: 1 }], { iterations: Infinity, duration: 800 });
    }
    const dmOver = e => {
        const row = e.target.closest && e.target.closest('.dm-info-row');
        if (!row) return;
        if (!dmBtn) {
            dmBtn = document.createElement('span');
            dmBtn.innerHTML = ICON + '<i style="position:absolute;right:-2px;top:-5px;font:9px/1 sans-serif;' +
                'font-style:normal;color:#fb7299;text-shadow:0 0 2px #fff"></i>';   // 与评论区楼层同一个放大镜
            dmBtn.title = '查这条弹幕的发送者成分';
            // 行本身是 position:relative，且时间列尾部本就空着一截：绝对定位钉进这条缝，
            // 不参与 flex 排版，正文一个像素都不会被顶动。尺寸写死在 svg 上，防被播放器样式表放大。
            dmBtn.style.cssText = 'position:absolute;top:50%;transform:translateY(-50%);' +
                'width:12px;height:12px;line-height:0;color:#fb7299;cursor:pointer;opacity:.85;z-index:2;' +
                // 播放器的样式表把 .dm-info-row 里的 span 一律设成 pointer-events:none，
                // 它自己的「屏蔽/举报」按钮再单独声明 auto。我们不挂类名，不声明就拿不到点击。
                'pointer-events:auto';
            dmBtn.firstChild.style.cssText = 'width:12px;height:12px;display:block';
            dmBtn.addEventListener('click', dmClick, true);
        }
        if (dmBtn.parentElement === row) return;
        row.appendChild(dmBtn);
        const tr = row.querySelector('.dm-info-time'), rr = row.getBoundingClientRect();
        dmBtn.style.left = Math.max(2, Math.round((tr ? tr.getBoundingClientRect().right : rr.left + 60) - rr.left - 16)) + 'px';
        dmPaint(row);
    };
    async function dmClick(e) {
        e.preventDefault(); e.stopPropagation();        // 行本身可点，别把跳转一起触发
        const btn = e.currentTarget, row = btn.parentElement;
        if (!row) return;
        const old = dmState.get(row);
        if (old?.busy) {                                // 进行中再点：给一次可见反馈，不重复发请求
            cfqPulse(btn, 'translateY(-50%) ');         // 这颗按钮的定位靠 translateY，动画里必须带上，否则会跳位
            return;
        }
        if (old?.uids?.length) {                        // 已解出过：再点就在候选间切换，不再发请求
            old.i = (old.i + 1) % old.uids.length;
            dmPaint(row);
            const n = old.uids.length;
            return runQuery(old.uids[old.i], n > 1 ? `弹幕候选 ${old.i + 1}/${n}` : '弹幕发送者');
        }
        const dm = row.querySelector('.dm-info-dm');
        const text = ((dm && (dm.getAttribute('title') || dm.textContent)) || '').trim();
        const t = (row.querySelector('.dm-info-time')?.textContent || '').trim().split(':').map(Number);
        if (!text || t.length < 2) return;
        const sec = t.length === 3 ? t[0] * 3600 + t[1] * 60 + t[2] : t[0] * 60 + t[1];
        const st = { busy: true, uids: null, i: 0, fail: '' };
        dmState.set(row, st);
        dmPaint(row);
        const r = await dmSenderOf(sec, text);
        st.busy = false;
        Object.assign(st, r.fail ? { fail: r.fail } : { uids: r.uids, i: 0 });
        dmPaint(row);                                   // 按钮已经搬去别行时这里什么都不做，结果仍留在这一行的状态里
        if (!r.fail) return runQuery(st.uids[0], st.uids.length > 1 ? `弹幕候选 1/${st.uids.length}` : '弹幕发送者');
        // 失败要响：面板开着就把原因显示在顶部，不能只塞进 tooltip
        if (state.query && !state.query.loading) { state.query.warn = r.fail; render(); }
    }
    function hookDmList() {
        const box = document.querySelector('.bpx-player-dm-container');
        if (!box || box === dmPanel) return;
        unhookDmList();
        box.addEventListener('mouseover', dmOver);
        dmPanel = box;
    }
    function unhookDmList() {
        if (!dmPanel) return;
        dmPanel.removeEventListener('mouseover', dmOver);
        dmSpin?.cancel(); dmSpin = null; dmSpinning = false;
        dmBtn?.remove(); dmBtn = null; dmPanel = null;
    }

    let warmed = false;

    function scan() {
        scanLive();
        try { state.dmList ? hookDmList() : unhookDmList(); }
        catch (e) { state.dmList = false; console.warn('[成分查询] 弹幕列表挂载失败，本次已自动停用该功能：', e); }
        const sr = commentRoot();
        if (!sr) {
            if (observedRoot) { mainObserver?.disconnect(); observedRoot = null; }
            return;
        }
        if (sr !== observedRoot) {
            mainObserver?.disconnect();
            mainObserver = new MutationObserver(schedule);
            mainObserver.observe(sr, { childList: true, subtree: true });
            observedRoot = sr;
            if (!warmed) { warmed = true; wbiKeys(); }   // 预热签名密钥，不阻塞首次查询
        }
        sr.querySelectorAll('bili-comment-thread-renderer').forEach(thread => {
            if (!seenThread.has(thread)) { seenThread.add(thread); observeShadow(thread); }
            const r = thread.shadowRoot?.querySelector('bili-comment-renderer');
            const header = headerOf(r);
            const uid = uidOf(r);
            readFloorDom(r?.shadowRoot, uid);
            autoTag(uid, header);
            mountFloorButton(header, uid);
            const rr = thread.shadowRoot?.querySelector('#replies')?.querySelector('bili-comment-replies-renderer');
            if (rr && !seenReplies.has(rr)) { seenReplies.add(rr); observeShadow(rr); }
            rr?.shadowRoot?.querySelectorAll('bili-comment-reply-renderer').forEach(el => {
                const s = el.shadowRoot;
                const main = s?.querySelector('#main') || s?.querySelector('#header') || headerOf(el);
                const ru = s?.querySelector('#user-avatar')?.dataset.userProfileId
                    || s?.querySelector('#user-name')?.dataset.userProfileId || uidOf(el);
                readFloorDom(s, ru);
                autoTag(ru, main);
                mountFloorButton(main, ru);
            });
        });
    }

    /* ══════════════ 启动：评论区会反复出现/销毁，不能一次性等待 ══════════════
     * 动态页/专栏页的评论区点击后才挂载、关闭即销毁成新节点，因此：
     *   - 捕获阶段监听点击，出现即挂观察器；1.2s 慢轮询只比一次根节点身份，兜住非点击展开（直播间 #chat-items 同理）；
     */
    loadRules();          // 必须先于 schedule：判定依赖 RULES，由它填充
    GM_setValue('cfq_floor_cache', null);   // 释放旧版标签缓存占用的空间，该键不再读取
    addEventListener('click', schedule, true);
    addEventListener('scroll', schedule, { passive: true, capture: true });
    setInterval(() => {
        if (commentRoot() !== observedRoot || document.getElementById('chat-items') !== liveRoot) schedule();
    }, 1200);
    schedule();
})();
