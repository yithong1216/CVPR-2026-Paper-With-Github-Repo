/* =======================================================================
   CVPR 2026 · An Atlas of Vision — interactive constellation engine
   Vanilla JS + Canvas2D. No dependencies. Tuned for phones.
   ======================================================================= */
(() => {
  "use strict";

  // ---- DOM ----
  const cv = document.getElementById("stage");
  const ctx = cv.getContext("2d", { alpha: true });
  const veil = document.getElementById("veil");
  const veilStatus = document.getElementById("veilStatus");
  const hint = document.getElementById("hint");

  const tip = document.createElement("div");
  tip.id = "tip"; document.body.appendChild(tip);

  // ---- State ----
  let DPR = Math.min(window.devicePixelRatio || 1, 2);
  let W = 0, H = 0;
  let G = null;                 // graph data
  let details = null;           // lazy papers.json
  let detailsLoading = null;

  let nodes = [];               // {bx,by,x,y,vx,vy,c,d,r,t,ph,af,aa}
  let adj = [];                 // adjacency list of indices
  let clusters = [];
  let links = [];

  // camera: world point at screen center + zoom
  const cam = { x: 0, y: 0, z: 1, tx: 0, ty: 0, tz: 1, anim: false };
  let MINZ = 0.16, MAXZ = 7;

  // interaction
  const pointers = new Map();
  let dragNode = -1, downNode = -1, downX = 0, downY = 0, downT = 0, moved = false, panning = false;
  let pinchDist = 0, pinchZoom = 1, pinchMX = 0, pinchMY = 0;
  let hoverNode = -1, selectedNode = -1;
  let lastMoveX = 0, lastMoveY = 0;

  // filters / highlight
  let activeCluster = -1;       // -1 = all
  let searchSet = null;         // Set of indices or null
  let neighborSet = null;       // Set for selected node highlight

  // glow sprites per cluster
  const sprites = [];
  let coreSprite = null;

  // spatial grid (from base positions)
  const CELL = 46;
  let grid = new Map();

  let t0 = performance.now();
  let needsRender = true;       // dirty flag for static frames

  // ---------------------------------------------------------------- utils
  const lerp = (a, b, t) => a + (b - a) * t;
  const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
  const fmt = n => n.toLocaleString("en-US");

  function hexToRgb(h) {
    const n = parseInt(h.slice(1), 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
  }
  function lighten([r, g, b], f) {
    return [Math.round(lerp(r, 255, f)), Math.round(lerp(g, 255, f)), Math.round(lerp(b, 255, f))];
  }

  // ---------------------------------------------------------- coordinate
  function worldToScreen(wx, wy) {
    return [(wx - cam.x) * cam.z + W / 2, (wy - cam.y) * cam.z + H / 2];
  }
  function screenToWorld(sx, sy) {
    return [(sx - W / 2) / cam.z + cam.x, (sy - H / 2) / cam.z + cam.y];
  }

  // ------------------------------------------------------------- sprites
  function buildSprites() {
    const S = 128;
    for (let i = 0; i < clusters.length; i++) {
      const off = document.createElement("canvas");
      off.width = off.height = S;
      const o = off.getContext("2d");
      const rgb = hexToRgb(clusters[i].color);
      const lite = lighten(rgb, .55);
      const g = o.createRadialGradient(S / 2, S / 2, 0, S / 2, S / 2, S / 2);
      g.addColorStop(0.0, `rgba(${lite[0]},${lite[1]},${lite[2]},0.95)`);
      g.addColorStop(0.18, `rgba(${rgb[0]},${rgb[1]},${rgb[2]},0.9)`);
      g.addColorStop(0.45, `rgba(${rgb[0]},${rgb[1]},${rgb[2]},0.32)`);
      g.addColorStop(1.0, `rgba(${rgb[0]},${rgb[1]},${rgb[2]},0)`);
      o.fillStyle = g;
      o.fillRect(0, 0, S, S);
      sprites[i] = off;
    }
    // bright achromatic core for selected/hover
    const off = document.createElement("canvas");
    off.width = off.height = S;
    const o = off.getContext("2d");
    const g = o.createRadialGradient(S / 2, S / 2, 0, S / 2, S / 2, S / 2);
    g.addColorStop(0, "rgba(255,255,255,1)");
    g.addColorStop(0.3, "rgba(255,247,230,0.55)");
    g.addColorStop(1, "rgba(255,240,210,0)");
    o.fillStyle = g; o.fillRect(0, 0, S, S);
    coreSprite = off;
  }

  // --------------------------------------------------------------- build
  function ingest(graph) {
    G = graph;
    clusters = graph.clusters;
    links = graph.links;
    const N = graph.nodes.length;
    adj = Array.from({ length: N }, () => []);
    for (const [a, b] of links) { adj[a].push(b); adj[b].push(a); }

    nodes = graph.nodes.map((n, i) => {
      const d = n.d || 0;
      return {
        bx: n.x, by: n.y, x: n.x, y: n.y, vx: 0, vy: 0,
        c: n.c, d, r: 2.1 + Math.sqrt(d) * 1.05, t: n.t,
        ph: Math.random() * Math.PI * 2,
        af: 0.18 + Math.random() * 0.5,             // wander freq
        aa: 1.6 + Math.random() * 4.2,              // wander amplitude (world)
        intro: 0,                                   // 0..1 reveal
      };
    });

    // intro: start collapsed toward center, expand with stagger
    for (let i = 0; i < N; i++) {
      const n = nodes[i];
      n.x = n.bx * 0.04; n.y = n.by * 0.04;
    }

    buildGrid();
    buildSprites();
    fitView(true);
  }

  function buildGrid() {
    grid.clear();
    for (let i = 0; i < nodes.length; i++) {
      const gx = Math.floor(nodes[i].bx / CELL), gy = Math.floor(nodes[i].by / CELL);
      const k = gx + "," + gy;
      let arr = grid.get(k); if (!arr) grid.set(k, arr = []);
      arr.push(i);
    }
  }

  function fitView(instant) {
    let minx = 1e9, miny = 1e9, maxx = -1e9, maxy = -1e9;
    for (const n of nodes) { if (n.bx < minx) minx = n.bx; if (n.bx > maxx) maxx = n.bx; if (n.by < miny) miny = n.by; if (n.by > maxy) maxy = n.by; }
    const cx = (minx + maxx) / 2, cy = (miny + maxy) / 2;
    const pad = 90;
    const zx = (W - pad * 2) / (maxx - minx), zy = (H - pad * 2) / (maxy - miny);
    let z = Math.min(zx, zy);
    MINZ = Math.min(0.16, z * 0.7);
    z = clamp(z, MINZ, MAXZ);
    cam.tx = cx; cam.ty = cy; cam.tz = z;
    if (instant) { cam.x = cx; cam.y = cy; cam.z = z; }
  }

  // --------------------------------------------------------------- resize
  function resize() {
    DPR = Math.min(window.devicePixelRatio || 1, 2);
    W = window.innerWidth; H = window.innerHeight;
    cv.width = Math.floor(W * DPR); cv.height = Math.floor(H * DPR);
    cv.style.width = W + "px"; cv.style.height = H + "px";
    ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    needsRender = true;
  }
  window.addEventListener("resize", resize);

  // --------------------------------------------------------------- physics
  const SPRING = 0.014, DAMP = 0.86, PULL = 0.035;
  function physics(dt) {
    const N = nodes.length;
    let introDone = true;
    for (let i = 0; i < N; i++) {
      const n = nodes[i];
      if (n.intro < 1) { n.intro = Math.min(1, n.intro + dt * 0.45); introDone = false; }
      // intro easing toward base
      if (n.intro < 1) {
        const e = 1 - Math.pow(1 - n.intro, 3);
        n.x = lerp(n.bx * 0.04, n.bx, e);
        n.y = lerp(n.by * 0.04, n.by, e);
        continue;
      }
      if (i === dragNode) continue;
      // spring to base
      n.vx = (n.vx + (n.bx - n.x) * SPRING) * DAMP;
      n.vy = (n.vy + (n.by - n.y) * SPRING) * DAMP;
      n.x += n.vx; n.y += n.vy;
    }
    // drag elasticity: pull neighbors toward dragged node
    if (dragNode >= 0) {
      const d = nodes[dragNode];
      for (const j of adj[dragNode]) {
        const n = nodes[j];
        n.vx += (d.x - n.x) * PULL;
        n.vy += (d.y - n.y) * PULL;
      }
    }
    return introDone;
  }

  // --------------------------------------------------------------- render
  function clusterRGB(i) { return clusters[i].color; }

  function alphaFor(i) {
    // dimming logic for search / cluster isolation / selection
    if (selectedNode >= 0) {
      if (i === selectedNode) return 1;
      if (neighborSet && neighborSet.has(i)) return 0.92;
      return 0.10;
    }
    if (searchSet) return searchSet.has(i) ? 1 : 0.07;
    if (activeCluster >= 0) return nodes[i].c === activeCluster ? 1 : 0.08;
    return 1;
  }

  function render(now) {
    const t = (now - t0) / 1000;

    // camera easing toward target
    if (cam.anim) {
      cam.x = lerp(cam.x, cam.tx, 0.12);
      cam.y = lerp(cam.y, cam.ty, 0.12);
      cam.z = lerp(cam.z, cam.tz, 0.12);
      if (Math.abs(cam.x - cam.tx) < 0.4 && Math.abs(cam.y - cam.ty) < 0.4 && Math.abs(cam.z - cam.tz) < 0.001) {
        cam.x = cam.tx; cam.y = cam.ty; cam.z = cam.tz; cam.anim = false;
      }
    }

    ctx.clearRect(0, 0, W, H);

    // compute render positions (physics + wander) and screen coords
    const N = nodes.length;
    const px = renderBuf.px, py = renderBuf.py, sx = renderBuf.sx, sy = renderBuf.sy, vis = renderBuf.vis;
    const z = cam.z;
    const margin = 60;
    for (let i = 0; i < N; i++) {
      const n = nodes[i];
      const wob = n.intro >= 1 ? 1 : 0;
      const wx = n.x + Math.sin(t * n.af + n.ph) * n.aa * wob;
      const wy = n.y + Math.cos(t * n.af * 0.9 + n.ph) * n.aa * wob;
      px[i] = wx; py[i] = wy;
      const X = (wx - cam.x) * z + W / 2, Y = (wy - cam.y) * z + H / 2;
      sx[i] = X; sy[i] = Y;
      vis[i] = (X >= -margin && X <= W + margin && Y >= -margin && Y <= H + margin) ? 1 : 0;
    }

    // ---- edges (single batched pass) ----
    const showLinks = linksOn && z > 0.28;
    if (showLinks) {
      const baseA = clamp((z - 0.28) * 0.5, 0.04, 0.22);
      ctx.lineWidth = clamp(z * 0.6, 0.5, 1.3);
      // normal threads
      ctx.strokeStyle = `rgba(150,170,220,${baseA})`;
      ctx.beginPath();
      for (let e = 0; e < links.length; e++) {
        const a = links[e][0], b = links[e][1];
        if (!vis[a] && !vis[b]) continue;
        if (selectedNode >= 0 && a !== selectedNode && b !== selectedNode) continue;
        if (activeCluster >= 0 && nodes[a].c !== activeCluster && nodes[b].c !== activeCluster) continue;
        ctx.moveTo(sx[a], sy[a]); ctx.lineTo(sx[b], sy[b]);
      }
      ctx.stroke();
    }
    // highlighted edges of selected node
    if (selectedNode >= 0) {
      ctx.lineWidth = 1.4;
      ctx.strokeStyle = "rgba(244,201,122,0.55)";
      ctx.beginPath();
      for (const j of adj[selectedNode]) {
        ctx.moveTo(sx[selectedNode], sy[selectedNode]); ctx.lineTo(sx[j], sy[j]);
      }
      ctx.stroke();
    }

    // ---- nodes (additive nebula) ----
    ctx.globalCompositeOperation = "lighter";
    const glowK = clamp(z * 0.9, 0.5, 2.4);
    for (let i = 0; i < N; i++) {
      if (!vis[i]) continue;
      if (i === selectedNode) continue;
      const a = alphaFor(i);
      if (a < 0.02) continue;
      const n = nodes[i];
      const rs = Math.max(1.3, n.r * z);
      const size = rs * 6 * glowK;
      ctx.globalAlpha = a;
      const sp = sprites[n.c];
      ctx.drawImage(sp, sx[i] - size / 2, sy[i] - size / 2, size, size);
    }
    ctx.globalAlpha = 1;

    // hovered node accent
    if (hoverNode >= 0 && hoverNode !== selectedNode && vis[hoverNode]) {
      const n = nodes[hoverNode];
      const rs = Math.max(2, n.r * z);
      const size = rs * 9;
      ctx.drawImage(coreSprite, sx[hoverNode] - size / 2, sy[hoverNode] - size / 2, size, size);
    }

    // selected node — brightest, on top
    if (selectedNode >= 0 && vis[selectedNode]) {
      const n = nodes[selectedNode];
      const rs = Math.max(3, n.r * z);
      const pulse = 1 + Math.sin(t * 3) * 0.08;
      const size = rs * 11 * pulse;
      ctx.drawImage(sprites[n.c], sx[selectedNode] - size / 2, sy[selectedNode] - size / 2, size, size);
      ctx.drawImage(coreSprite, sx[selectedNode] - rs * 4 / 2, sy[selectedNode] - rs * 4 / 2, rs * 4, rs * 4);
    }
    ctx.globalCompositeOperation = "source-over";

    // ---- labels (selected / hovered / sparse search) ----
    ctx.textBaseline = "middle";
    if (selectedNode >= 0 && vis[selectedNode]) drawLabel(selectedNode, sx[selectedNode], sy[selectedNode], true);
    if (hoverNode >= 0 && hoverNode !== selectedNode && vis[hoverNode]) drawLabel(hoverNode, sx[hoverNode], sy[hoverNode], false);
    if (searchSet && searchSet.size <= 16) {
      ctx.font = '500 12px "Hanken Grotesk", sans-serif';
      for (const i of searchSet) if (vis[i]) drawLabel(i, sx[i], sy[i], false);
    }
  }

  function drawLabel(i, X, Y, big) {
    const n = nodes[i];
    let s = n.t.length > 64 ? n.t.slice(0, 62) + "…" : n.t;
    ctx.font = (big ? '600 14px' : '500 12px') + ' "Hanken Grotesk", sans-serif';
    const w = ctx.measureText(s).width;
    const padX = 9, padY = 5, off = Math.max(8, n.r * cam.z) + 8;
    let lx = X + off, ly = Y;
    if (lx + w + padX * 2 > W - 8) lx = X - off - w - padX * 2;
    ctx.fillStyle = "rgba(8,10,18,0.82)";
    roundRect(lx - padX, ly - 11 - padY, w + padX * 2, 22 + padY * 2, 8);
    ctx.fill();
    ctx.fillStyle = "#eef1f8";
    ctx.fillText(s, lx, ly + 1);
  }
  function roundRect(x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  const renderBuf = { px: null, py: null, sx: null, sy: null, vis: null };

  // ----------------------------------------------------------- main loop
  let lastT = performance.now();
  function loop(now) {
    const dt = Math.min(0.05, (now - lastT) / 1000); lastT = now;
    physics(dt);
    render(now);
    requestAnimationFrame(loop);
  }

  // ----------------------------------------------------------- hit-test
  function hitTest(sxp, syp) {
    // convert to world, search nearby grid cells
    const [wx, wy] = screenToWorld(sxp, syp);
    const gx = Math.floor(wx / CELL), gy = Math.floor(wy / CELL);
    let best = -1, bestD = 1e9;
    const tol = 16 / cam.z; // screen px tolerance -> world
    const R = Math.max(1, Math.ceil(tol / CELL) + 1);
    for (let dx = -R; dx <= R; dx++) for (let dy = -R; dy <= R; dy++) {
      const arr = grid.get((gx + dx) + "," + (gy + dy));
      if (!arr) continue;
      for (const i of arr) {
        // use live screen pos
        const ddx = renderBuf.sx[i] - sxp, ddy = renderBuf.sy[i] - syp;
        const d = ddx * ddx + ddy * ddy;
        const hitR = Math.max(9, nodes[i].r * cam.z + 7);
        if (d < hitR * hitR && d < bestD) { bestD = d; best = i; }
      }
    }
    return best;
  }

  // ----------------------------------------------------------- pointer
  function getXY(e) { return [e.clientX, e.clientY]; }

  cv.addEventListener("pointerdown", e => {
    cv.setPointerCapture(e.pointerId);
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (pointers.size === 2) {
      const p = [...pointers.values()];
      pinchDist = Math.hypot(p[0].x - p[1].x, p[0].y - p[1].y);
      pinchZoom = cam.z;
      pinchMX = (p[0].x + p[1].x) / 2; pinchMY = (p[0].y + p[1].y) / 2;
      panning = false; dragNode = -1; downNode = -1;
      return;
    }
    cam.anim = false;
    downX = e.clientX; downY = e.clientY; downT = performance.now(); moved = false;
    lastMoveX = e.clientX; lastMoveY = e.clientY;
    const hit = hitTest(e.clientX, e.clientY);
    downNode = hit;
    if (hit >= 0) { panning = false; } else { panning = true; }
  });

  cv.addEventListener("pointermove", e => {
    if (pointers.has(e.pointerId)) pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

    // pinch
    if (pointers.size === 2) {
      const p = [...pointers.values()];
      const d = Math.hypot(p[0].x - p[1].x, p[0].y - p[1].y);
      if (pinchDist > 0) {
        const nz = clamp(pinchZoom * (d / pinchDist), MINZ, MAXZ);
        zoomAt(pinchMX, pinchMY, nz);
      }
      return;
    }

    if (!pointers.has(e.pointerId) && hoverNode === -1 && e.pointerType === "mouse") {
      // hover handling for mouse when not pressing
    }

    const dx = e.clientX - lastMoveX, dy = e.clientY - lastMoveY;

    if (pointers.has(e.pointerId)) {
      // a button/touch is down
      if (Math.abs(e.clientX - downX) + Math.abs(e.clientY - downY) > 5) moved = true;

      if (panning) {
        cam.x -= dx / cam.z; cam.y -= dy / cam.z;
      } else if (downNode >= 0 && moved) {
        // start/continue dragging the node
        dragNode = downNode;
        const [wx, wy] = screenToWorld(e.clientX, e.clientY);
        const n = nodes[dragNode]; n.x = wx; n.y = wy; n.vx = 0; n.vy = 0;
        hideTip();
      }
      lastMoveX = e.clientX; lastMoveY = e.clientY;
    } else if (e.pointerType === "mouse") {
      // hover
      const hit = hitTest(e.clientX, e.clientY);
      if (hit !== hoverNode) {
        hoverNode = hit;
        if (hit >= 0) showTipFor(hit, e.clientX, e.clientY); else hideTip();
        cv.style.cursor = hit >= 0 ? "pointer" : "grab";
      } else if (hit >= 0) {
        moveTip(e.clientX, e.clientY);
      }
    }
  });

  function endPointer(e) {
    const wasDown = pointers.has(e.pointerId);
    pointers.delete(e.pointerId);
    if (pointers.size < 2) pinchDist = 0;

    if (pointers.size === 0 && wasDown) {
      const dt = performance.now() - downT;
      if (!moved && dt < 450 && downNode >= 0) {
        selectNode(downNode, false);
      } else if (!moved && dt < 350 && downNode < 0) {
        // tap empty -> dismiss selection
        if (selectedNode >= 0) deselect();
      }
      dragNode = -1; downNode = -1; panning = false;
      dismissHint();
    }
  }
  cv.addEventListener("pointerup", endPointer);
  cv.addEventListener("pointercancel", endPointer);
  cv.addEventListener("pointerleave", e => { if (e.pointerType === "mouse") { hoverNode = -1; hideTip(); } });

  // wheel zoom
  cv.addEventListener("wheel", e => {
    e.preventDefault();
    const f = Math.exp(-e.deltaY * 0.0015);
    zoomAt(e.clientX, e.clientY, clamp(cam.z * f, MINZ, MAXZ));
  }, { passive: false });

  function zoomAt(sxp, syp, nz) {
    const [wx, wy] = screenToWorld(sxp, syp);
    cam.z = nz;
    // keep (wx,wy) under cursor
    cam.x = wx - (sxp - W / 2) / cam.z;
    cam.y = wy - (syp - H / 2) / cam.z;
    cam.anim = false;
  }

  // -------------------------------------------------------------- tooltip
  function showTipFor(i, x, y) {
    tip.textContent = nodes[i].t;
    tip.classList.add("show");
    moveTip(x, y);
  }
  function moveTip(x, y) {
    const r = tip.getBoundingClientRect();
    let lx = x + 16, ly = y + 16;
    if (lx + r.width > W - 8) lx = x - r.width - 16;
    if (ly + r.height > H - 8) ly = y - r.height - 16;
    tip.style.left = lx + "px"; tip.style.top = ly + "px";
  }
  function hideTip() { tip.classList.remove("show"); }

  // ----------------------------------------------------------- selection
  function selectNode(i, recenter) {
    selectedNode = i;
    neighborSet = new Set(adj[i]);
    hideTip(); hoverNode = -1;
    if (recenter) flyTo(nodes[i].bx, nodes[i].by, Math.max(cam.z, 1.1));
    openSheet(i);
    dismissHint();
  }
  function deselect() {
    selectedNode = -1; neighborSet = null;
    closeSheet();
  }
  function flyTo(wx, wy, z) {
    cam.tx = wx; cam.ty = wy; cam.tz = clamp(z, MINZ, MAXZ); cam.anim = true;
  }

  // --------------------------------------------------------------- veil
  function hideVeil() {
    veil.classList.add("gone");
    setTimeout(() => { veil.style.display = "none"; }, 900);
  }

  // ------------------------------------------------------- details / sheet
  const sheet = document.getElementById("sheet");
  const sheetScroll = document.getElementById("sheetScroll");
  const sheetScrim = document.getElementById("sheetScrim");
  document.getElementById("sheetClose").addEventListener("click", deselect);
  sheetScrim.addEventListener("click", deselect);

  async function ensureDetails() {
    if (details) return details;
    if (detailsLoading) return detailsLoading;
    detailsLoading = fetch("data/papers.json").then(r => r.json()).then(d => { details = d; return d; });
    return detailsLoading;
  }

  function linkSvg(kind) {
    const m = {
      page: '<path d="M14 3h7v7M21 3l-9 9M5 7v12h12"/>',
      pdf: '<path d="M7 3h7l5 5v13H7z"/><path d="M14 3v5h5"/>',
      arx: '<path d="M3 12h18M12 3v18"/>',
      code: '<path d="M8 9l-4 3 4 3M16 9l4 3-4 3M13 6l-2 12"/>'
    };
    return `<svg viewBox="0 0 24 24">${m[kind] || m.page}</svg>`;
  }

  async function openSheet(i) {
    sheet.classList.remove("hidden");
    sheetScrim.classList.remove("hidden");
    sheetScroll.scrollTop = 0;
    const cl = clusters[nodes[i].c];
    const titleFallback = nodes[i].t;
    sheetScroll.innerHTML = `
      <span class="p-chip"><i style="background:${cl.color};color:${cl.color}"></i>${cl.label}</span>
      <h2 class="p-title">${esc(titleFallback)}</h2>
      <div class="p-authors" id="pAuthors">Loading details…</div>
    `;
    const data = await ensureDetails();
    if (selectedNode !== i) return; // changed while loading
    const p = data[i] || {};
    const authors = p.au && p.au.length ? p.au : [];
    let authorHtml = "";
    if (authors.length) {
      const shown = authors.slice(0, 8).join(", ");
      const extra = authors.length > 8 ? ` <span class="more" id="authMore">+${authors.length - 8} more</span>` : "";
      authorHtml = esc(shown) + extra;
    } else authorHtml = "—";

    const links = [];
    if (p.pdf) links.push(`<a class="p-link primary" href="${p.pdf}" target="_blank" rel="noopener">${linkSvg("pdf")} PDF</a>`);
    if (p.arx) links.push(`<a class="p-link" href="${p.arx}" target="_blank" rel="noopener">${linkSvg("arx")} arXiv</a>`);
    if (p.code) links.push(`<a class="p-link" href="${p.code}" target="_blank" rel="noopener">${linkSvg("code")} Code</a>`);
    if (p.u) links.push(`<a class="p-link" href="${p.u}" target="_blank" rel="noopener">${linkSvg("page")} CVF</a>`);

    // related papers (neighbors, by edge)
    const rel = adj[i].slice().sort((a, b) => nodes[b].d - nodes[a].d).slice(0, 8);
    const relHtml = rel.map(j => {
      const c = clusters[nodes[j].c];
      return `<div class="p-rel" data-i="${j}">
        <span class="p-rel-dot" style="background:${c.color};color:${c.color}"></span>
        <div><div class="p-rel-t">${esc(nodes[j].t)}</div><div class="p-rel-c">${c.label}</div></div>
      </div>`;
    }).join("");

    sheetScroll.innerHTML = `
      <span class="p-chip"><i style="background:${cl.color};color:${cl.color}"></i>${cl.label}</span>
      <h2 class="p-title">${esc(p.t || titleFallback)}</h2>
      <div class="p-authors">${authorHtml}</div>
      ${p.ab ? `<p class="p-section-label">Abstract</p><p class="p-abstract">${esc(p.ab)}</p>` : ""}
      ${links.length ? `<div class="p-links">${links.join("")}</div>` : ""}
      ${relHtml ? `<div class="p-divider"></div><p class="p-section-label">Related papers</p><div class="p-related">${relHtml}</div>` : ""}
    `;
    const am = document.getElementById("authMore");
    if (am) am.addEventListener("click", () => { am.parentElement.textContent = authors.join(", "); });
    sheetScroll.querySelectorAll(".p-rel").forEach(el => {
      el.addEventListener("click", () => selectNode(+el.dataset.i, true));
    });
  }
  function closeSheet() {
    sheet.classList.add("hidden");
    sheetScrim.classList.add("hidden");
  }
  function esc(s) { return (s || "").replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])); }

  // --------------------------------------------------------------- search
  const search = document.getElementById("search");
  const searchPill = search.closest(".search-pill");
  const results = document.getElementById("results");
  const searchClear = document.getElementById("searchClear");
  let searchTimer = 0;

  search.addEventListener("input", () => {
    searchPill.classList.toggle("filled", search.value.length > 0);
    clearTimeout(searchTimer);
    searchTimer = setTimeout(runSearch, 110);
  });
  searchClear.addEventListener("click", () => {
    search.value = ""; searchPill.classList.remove("filled"); runSearch(); search.focus();
  });

  function runSearch() {
    const q = search.value.trim().toLowerCase();
    if (!q) { searchSet = null; results.classList.remove("show"); results.innerHTML = ""; return; }
    const terms = q.split(/\s+/);
    const hits = [];
    for (let i = 0; i < nodes.length; i++) {
      const t = nodes[i].t.toLowerCase();
      const cl = clusters[nodes[i].c].label.toLowerCase();
      let ok = true;
      for (const term of terms) { if (t.indexOf(term) < 0 && cl.indexOf(term) < 0) { ok = false; break; } }
      if (ok) hits.push(i);
    }
    searchSet = new Set(hits);
    // results list (top 40)
    if (hits.length === 0) {
      results.innerHTML = `<div class="res-empty">No papers found</div>`;
    } else {
      const top = hits.slice(0, 40);
      results.innerHTML = top.map(i => {
        const c = clusters[nodes[i].c];
        return `<div class="res-item" data-i="${i}">
          <div><span class="res-dot" style="background:${c.color}"></span><span class="res-title">${esc(nodes[i].t)}</span></div>
          <div class="res-meta">${c.label}${hits.length > 40 ? "" : ""}</div>
        </div>`;
      }).join("") + (hits.length > 40 ? `<div class="res-empty">+${hits.length - 40} more — refine your search</div>` : "");
    }
    results.classList.add("show");
    results.querySelectorAll(".res-item").forEach(el => {
      el.addEventListener("click", () => {
        const i = +el.dataset.i;
        results.classList.remove("show");
        selectNode(i, true);
      });
    });
  }

  // --------------------------------------------------------------- legend
  const legend = document.getElementById("legend");
  const legendBody = document.getElementById("legendBody");
  document.getElementById("btnLegend").addEventListener("click", () => {
    legend.classList.toggle("hidden");
    document.getElementById("btnLegend").classList.toggle("on", !legend.classList.contains("hidden"));
  });
  document.getElementById("legendClose").addEventListener("click", () => {
    legend.classList.add("hidden"); document.getElementById("btnLegend").classList.remove("on");
  });
  document.getElementById("legendAll").addEventListener("click", () => { activeCluster = -1; paintLegend(); });

  function buildLegend() {
    const order = clusters.map((c, i) => i).sort((a, b) => clusters[b].size - clusters[a].size);
    legendBody.innerHTML = order.map(i => {
      const c = clusters[i];
      return `<div class="leg" data-i="${i}">
        <span class="leg-dot" style="background:${c.color};color:${c.color}"></span>
        <span class="leg-name">${c.label}</span>
        <span class="leg-n">${c.size}</span>
      </div>`;
    }).join("");
    legendBody.querySelectorAll(".leg").forEach(el => {
      el.addEventListener("click", () => {
        const i = +el.dataset.i;
        activeCluster = (activeCluster === i) ? -1 : i;
        if (activeCluster >= 0) { deselect(); searchSet = null; search.value = ""; searchPill.classList.remove("filled"); results.classList.remove("show"); }
        paintLegend();
      });
    });
  }
  function paintLegend() {
    legendBody.querySelectorAll(".leg").forEach(el => {
      el.classList.toggle("dim", activeCluster >= 0 && +el.dataset.i !== activeCluster);
    });
  }

  // controls
  document.getElementById("btnReset").addEventListener("click", () => {
    activeCluster = -1; paintLegend();
    deselect();
    fitView(false); cam.anim = true;
  });
  let linksOn = true;
  const btnLinks = document.getElementById("btnLinks");
  btnLinks.classList.add("on");
  btnLinks.addEventListener("click", () => {
    linksOn = !linksOn; btnLinks.classList.toggle("on", linksOn);
  });

  let hintDismissed = false;
  function dismissHint() { if (!hintDismissed) { hintDismissed = true; hint.classList.add("gone"); } }
  setTimeout(dismissHint, 7000);

  // keyboard
  window.addEventListener("keydown", e => {
    if (e.key === "Escape") { if (selectedNode >= 0) deselect(); else { search.value = ""; runSearch(); } }
    if (e.key === "/" && document.activeElement !== search) { e.preventDefault(); search.focus(); }
  });

  // ------------------------------------------------------------- boot
  function setCounts() {
    document.getElementById("countPapers").textContent = fmt(G.nodes.length);
    document.getElementById("countTopics").textContent = clusters.length;
    document.getElementById("countLinks").textContent = fmt(links.length);
  }

  // visible error banner (so failures are never silent)
  window.addEventListener("error", ev => {
    let b = document.getElementById("errBanner");
    if (!b) {
      b = document.createElement("div"); b.id = "errBanner";
      b.style.cssText = "position:fixed;left:0;right:0;top:0;z-index:999;background:#b3261e;color:#fff;font:13px monospace;padding:8px 12px;white-space:pre-wrap";
      document.body.appendChild(b);
    }
    b.textContent = "JS error: " + (ev.message || ev.error) + " @ " + (ev.filename || "") + ":" + (ev.lineno || "");
  });

  resize();
  veilStatus.textContent = "Loading 4,069 papers…";
  fetch("data/graph.json")
    .then(r => r.json())
    .then(graph => {
      ingest(graph);
      renderBuf.px = new Float32Array(nodes.length);
      renderBuf.py = new Float32Array(nodes.length);
      renderBuf.sx = new Float32Array(nodes.length);
      renderBuf.sy = new Float32Array(nodes.length);
      renderBuf.vis = new Uint8Array(nodes.length);
      setCounts();
      buildLegend();
      t0 = performance.now(); lastT = t0;
      requestAnimationFrame(loop);
      setTimeout(hideVeil, 350);
      // warm the details file shortly after first paint (non-blocking)
      setTimeout(() => ensureDetails().catch(() => {}), 1800);
      // self-test hook: ?test or #test auto-opens the highest-degree paper
      if (location.hash.indexOf("test") >= 0 || location.search.indexOf("test") >= 0) {
        let best = 0; for (let i = 1; i < nodes.length; i++) if (nodes[i].d > nodes[best].d) best = i;
        setTimeout(() => selectNode(best, true), 1200);
      }
      if (location.search.indexOf("demo") >= 0) {
        setTimeout(() => {
          legend.classList.remove("hidden"); document.getElementById("btnLegend").classList.add("on");
          search.value = "diffusion"; searchPill.classList.add("filled"); runSearch();
          dismissHint();
        }, 1300);
      }
    })
    .catch(err => {
      veilStatus.textContent = "Failed to load graph data.";
      console.error(err);
    });
})();
