/* doory — phone poster desk. MIT, see LICENSE.txt.
   idea after @shaongitbd (shaongitbd/doory); clean-room implementation, no code copied. */
(function () {
  "use strict";
  var DW = 360, DH = 640;
  var KEY = "doory.guest.v1";
  var SERIF = '"Playfair Display", Didot, "Bodoni MT", Georgia, "Liberation Serif", serif';
  var SANS = 'system-ui, "Avenir Next", "Gill Sans", "Helvetica Neue", Helvetica, sans-serif';
  var COLORS = ["#f6efe4", "#1a2740", "#e25a2a", "#ff9a3c", "#f0c14e", "#2f6b4f", "#d4526e", "#3d6f8f"];

  var cv = document.getElementById("canvas");
  var stage = document.getElementById("stage");
  var panel = document.getElementById("panel");
  var words = document.getElementById("words");
  var ctx = cv.getContext("2d");
  var mctx = document.createElement("canvas").getContext("2d");
  if (!ctx || !mctx) return;

  var nid = 1;
  var doc = null;
  var sel = -1;
  var hist = [];
  var guides = { v: null, h: null };
  var view = { vw: 1, vh: 1, ox: 0, oy: 0, s: 1, dpr: 1 };
  var ptrs = {};
  var gesture = null;
  var pinching = false;
  var wheelSnap = false;
  var wheelT = 0;
  var saveT = 0;
  var readySent = false;
  var accentI = 0;
  var grainSrc = null;
  var grainPat = null;
  var grainCtx = null;
  var motes = [];
  var knots = [];

  function rndFn(seed) {
    var a = seed >>> 0;
    return function () {
      a = (a * 1664525 + 1013904223) >>> 0;
      return a / 4294967296;
    };
  }
  var rnd = rndFn(11);
  var i;
  for (i = 0; i < 16; i++) motes.push({ x: rnd(), y: rnd(), r: 0.7 + rnd() * 1.5, v: 0.008 + rnd() * 0.012, a: 0.12 + rnd() * 0.18 });
  for (i = 0; i < 10; i++) knots.push({ x: rnd(), y: rnd(), r: 1.4 + rnd() * 2.6, a: 0.035 + rnd() * 0.04 });

  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function clone(o) {
    var n = {};
    for (var k in o) n[k] = o[k];
    return n;
  }
  function hexToRgb(hex) {
    var h = String(hex || "#000").replace("#", "");
    if (h.length === 3) h = h.charAt(0) + h.charAt(0) + h.charAt(1) + h.charAt(1) + h.charAt(2) + h.charAt(2);
    var n = parseInt(h, 16);
    if (!isFinite(n)) n = 0;
    return { r: (n >> 16) & 255, g: (n >> 8) & 255, b: n & 255 };
  }
  function rgbToHex(r, g, b) {
    function c(v) {
      v = clamp(v | 0, 0, 255);
      var s = v.toString(16);
      return s.length < 2 ? "0" + s : s;
    }
    return "#" + c(r) + c(g) + c(b);
  }
  function shade(hex, amt) {
    var c = hexToRgb(hex);
    return rgbToHex(c.r + amt, c.g + amt, c.b + amt);
  }
  function hexA(hex, a) {
    var c = hexToRgb(hex);
    return "rgba(" + c.r + "," + c.g + "," + c.b + "," + a + ")";
  }
  function lum(hex) {
    var c = hexToRgb(hex);
    return (0.2126 * c.r + 0.7152 * c.g + 0.0722 * c.b) / 255;
  }
  function fontOf(it) {
    return (it.italic ? "italic " : "") + (it.weight || 700) + " " + (it.size || 16) + "px " + (it.font || SERIF);
  }
  function textWidth(c, it) {
    var s = it.text || "";
    var track = it.track || 0;
    if (!s.length) return 0;
    if (!track) return c.measureText(s).width;
    var w = 0;
    for (var n = 0; n < s.length; n++) w += c.measureText(s.charAt(n)).width;
    return w + track * (s.length - 1);
  }
  function measure(it) {
    if (it.type !== "text") return;
    mctx.font = fontOf(it);
    var s = it.text || "";
    var cx = it.x + (it.w || 0) / 2;
    var cy = it.y + (it.h || 0) / 2;
    if (!s.length) {
      it.h = Math.max(16, (it.size || 16) * 1.25);
      return;
    }
    it.w = Math.max(12, textWidth(mctx, it) + 4);
    it.h = Math.max(12, (it.size || 16) * 1.12);
    it.x = cx - it.w / 2;
    it.y = cy - it.h / 2;
  }
  function fitLine(it, maxW) {
    var guard = 0;
    measure(it);
    while (it.w > maxW && it.size > 11 && guard < 48) {
      it.size *= 0.96;
      if (it.track) it.track *= 0.96;
      measure(it);
      guard++;
    }
  }
  function place(it, cx, cy) {
    it.x = cx - it.w / 2;
    it.y = cy - it.h / 2;
  }
  function stackLines(list, cx, top, gaps) {
    var y = top;
    for (var n = 0; n < list.length; n++) {
      fitLine(list[n], 312);
      place(list[n], cx, y + list[n].h / 2);
      y += list[n].h + (gaps[n] == null ? 8 : gaps[n]);
    }
    return y;
  }
  function E(p) {
    p.id = nid++;
    if (p.rot == null) p.rot = 0;
    if (p.op == null) p.op = 1;
    return p;
  }
  function reindex() {
    nid = 1;
    for (var n = 0; n < doc.items.length; n++) {
      var id = doc.items[n].id;
      if (!(id > 0)) doc.items[n].id = nid++;
      else if (id >= nid) nid = id + 1;
    }
  }

  function seedLantern() {
    nid = 1;
    var items = [];
    function add(p) { var it = E(p); items.push(it); return it; }
    add({ type: "ellipse", x: 18, y: 70, w: 104, h: 104, fill: "#f7f1e2" });
    add({ type: "ellipse", x: 58, y: 96, w: 28, h: 22, fill: "#e4d3b4", op: 0.85 });
    add({ type: "ellipse", x: 300, y: 96, w: 5, h: 5, fill: "#f6efe4" });
    add({ type: "ellipse", x: 262, y: 124, w: 3, h: 3, fill: "#f6efe4", op: 0.85 });
    add({ type: "ellipse", x: 328, y: 168, w: 4, h: 4, fill: "#f6efe4", op: 0.75 });
    add({ type: "star", x: 308, y: 132, w: 14, h: 14, fill: "#f4ead8", rot: 0.25 });
    add({ type: "door", x: 72, y: 118, w: 216, h: 336, fill: "#121a26" });
    add({ type: "rect", x: 178, y: 146, w: 3, h: 78, r: 1, fill: "#f3ead7", op: 0.85 });
    add({ type: "rect", x: 156, y: 214, w: 48, h: 14, r: 3, fill: "#f3ead7" });
    add({ type: "ellipse", x: 128, y: 222, w: 104, h: 104, fill: "#ff8a2a", glow: 1 });
    add({ type: "ellipse", x: 154, y: 248, w: 52, h: 52, fill: "#ffe6b0", flicker: 1 });
    add({ type: "frame", x: 72, y: 118, w: 216, h: 336, fill: "#f4ead8", ink: "#e7c27a", stroke: 15 });
    add({ type: "rect", x: 92, y: 432, w: 176, h: 10, r: 2, fill: "#e6d5bc" });
    add({ type: "ellipse", x: 108, y: 448, w: 144, h: 26, fill: "#ffb15a", op: 0.22 });
    add({ type: "sprig", x: 26, y: 392, w: 54, h: 82, fill: "#d7e4b8", rot: -0.2 });
    add({ type: "badge", x: 226, y: 386, w: 76, h: 76, fill: "#f0c14e", ink: "#1c2430", text: "8 PM" });
    var kick = add({ type: "text", text: "SATURDAY NIGHT", size: 12, weight: 600, track: 1.6, font: SANS, fill: "#f4ead8", x: 0, y: 0, w: 10, h: 10 });
    fitLine(kick, 220);
    place(kick, 180, 46);
    var lineA = add({ type: "text", text: "LANTERN", size: 24, weight: 700, track: 6, font: SERIF, fill: "#1c2430", x: 0, y: 0, w: 10, h: 10 });
    var lineB = add({ type: "text", text: "WALK", size: 82, weight: 700, track: 1, font: SERIF, fill: "#1c2430", x: 0, y: 0, w: 10, h: 10 });
    var lineC = add({ type: "text", text: "maple court", size: 13, weight: 600, track: 2.4, font: SANS, fill: "#6e5848", x: 0, y: 0, w: 10, h: 10 });
    var guard = 0;
    stackLines([lineA, lineB, lineC], 180, 478, [4, 14, 0]);
    while (lineC.y + lineC.h > DH - 26 && lineB.size > 52 && guard < 8) {
      lineB.size *= 0.94;
      stackLines([lineA, lineB, lineC], 180, 478, [4, 14, 0]);
      guard++;
    }
    add({ type: "rect", x: 152, y: lineB.y + lineB.h + 4, w: 56, h: 3, r: 1.5, fill: "#e25a2a" });
    return {
      kind: "lantern",
      name: "Lantern walk",
      paper: "#1a2740",
      paper2: "#101820",
      band: "#f6efe4",
      bandY: 446,
      items: items
    };
  }

  function seedInvite() {
    nid = 1;
    var items = [];
    function add(p) { var it = E(p); items.push(it); return it; }
    add({ type: "ellipse", x: 178, y: 28, w: 156, h: 156, fill: "#e25a2a" });
    add({ type: "ellipse", x: 214, y: 62, w: 64, h: 64, fill: "#f6efe4", op: 0.2 });
    add({ type: "star", x: 34, y: 64, w: 40, h: 40, fill: "#f0c14e", rot: 0.2 });
    add({ type: "sprig", x: 280, y: 470, w: 48, h: 74, fill: "#2f6b4f", rot: 0.4 });
    var a = add({ type: "text", text: "YOU ARE", size: 15, weight: 600, track: 4.2, font: SANS, fill: "#8a5344", x: 0, y: 0, w: 10, h: 10 });
    var b = add({ type: "text", text: "INVITED", size: 64, weight: 700, track: 1, font: SERIF, fill: "#1c2430", x: 0, y: 0, w: 10, h: 10 });
    var c = add({ type: "text", text: "sunday table", size: 22, weight: 500, italic: 1, font: SERIF, fill: "#1c2430", x: 0, y: 0, w: 10, h: 10, track: 0 });
    var d = add({ type: "text", text: "bring something warm", size: 15, weight: 500, track: 0.5, font: SANS, fill: "#6e5c50", x: 0, y: 0, w: 10, h: 10 });
    stackLines([a, b, c, d], 180, 214, [8, 16, 10, 0]);
    add({ type: "rect", x: 118, y: b.y + b.h + 6, w: 124, h: 3, r: 1.5, fill: "#e25a2a" });
    add({ type: "badge", x: 36, y: 548, w: 124, h: 52, fill: "#1c2430", ink: "#f6efe4", text: "SUNDAY" });
    return {
      kind: "invite",
      name: "Sunday table",
      paper: "#f6f0e6",
      paper2: "#efe2d0",
      band: null,
      bandY: 0,
      items: items
    };
  }

  function seedBlank() {
    nid = 1;
    var items = [];
    function add(p) { var it = E(p); items.push(it); return it; }
    var a = add({ type: "text", text: "Your headline", size: 40, weight: 700, font: SERIF, fill: "#1c2430", x: 0, y: 0, w: 10, h: 10, track: 0 });
    var b = add({ type: "text", text: "Drag me, then pinch", size: 16, weight: 500, font: SANS, fill: "#8a7b6c", x: 0, y: 0, w: 10, h: 10, track: 0.3 });
    fitLine(a, 300);
    place(a, 180, 286);
    fitLine(b, 280);
    place(b, 180, a.y + a.h + 16 + b.h / 2);
    return {
      kind: "blank",
      name: "Blank page",
      paper: "#f7f3ec",
      paper2: "#efe6d8",
      band: null,
      bandY: 0,
      items: items
    };
  }

  function validDoc(d) {
    if (!d || typeof d.paper !== "string" || !Array.isArray(d.items)) return false;
    for (var n = 0; n < d.items.length; n++) {
      var it = d.items[n];
      if (!it || typeof it.type !== "string") return false;
      if (!(it.w > 0) || !(it.h > 0)) return false;
    }
    return true;
  }
  function readStore() {
    try {
      var raw = localStorage.getItem(KEY);
      if (!raw) return null;
      var d = JSON.parse(raw);
      return validDoc(d) ? d : null;
    } catch (e) { return null; }
  }
  function save() {
    try { localStorage.setItem(KEY, JSON.stringify(doc)); } catch (e) {}
  }
  function saveSoon() {
    clearTimeout(saveT);
    saveT = setTimeout(save, 140);
  }
  function snapshot() {
    hist.push(JSON.stringify(doc));
    if (hist.length > 30) hist.shift();
  }
  function boot() {
    var stored = readStore();
    if (stored) doc = stored;
    else {
      doc = seedLantern();
      save();
    }
    reindex();
  }

  function pathRound(c, x, y, w, h, r) {
    var rr = Math.max(0, Math.min(r || 0, Math.min(w, h) / 2));
    c.beginPath();
    c.moveTo(x + rr, y);
    c.arcTo(x + w, y, x + w, y + h, rr);
    c.arcTo(x + w, y + h, x, y + h, rr);
    c.arcTo(x, y + h, x, y, rr);
    c.arcTo(x, y, x + w, y, rr);
    c.closePath();
  }
  function traceArch(c, w, h, closeBottom) {
    var r = Math.max(1, w / 2);
    c.beginPath();
    c.moveTo(0, h);
    c.lineTo(0, r);
    c.arc(r, r, r, Math.PI, 0, false);
    c.lineTo(w, h);
    if (closeBottom) c.closePath();
  }
  function withLocal(it, fn) {
    ctx.save();
    ctx.translate(it.x + it.w / 2, it.y + it.h / 2);
    ctx.rotate(it.rot || 0);
    ctx.translate(-it.w / 2, -it.h / 2);
    ctx.globalAlpha = it.op == null ? 1 : it.op;
    fn();
    ctx.restore();
  }
  function drawRect(it) {
    withLocal(it, function () {
      pathRound(ctx, 0, 0, it.w, it.h, it.r || 0);
      ctx.fillStyle = it.fill || "#fff";
      ctx.fill();
    });
  }
  function drawEllipse(it, t) {
    withLocal(it, function () {
      var cx = it.w / 2, cy = it.h / 2;
      var pulse = it.flicker ? 1 + Math.sin(t * 0.009 + (it.id || 0)) * 0.05 : 1;
      ctx.translate(cx, cy);
      ctx.scale(pulse, pulse);
      ctx.translate(-cx, -cy);
      if (it.glow) {
        var R = Math.max(it.w, it.h) * (1.28 + Math.sin(t * 0.003) * 0.08);
        var g = ctx.createRadialGradient(cx, cy, Math.min(it.w, it.h) * 0.12, cx, cy, R);
        g.addColorStop(0, hexA(it.fill, 0.7));
        g.addColorStop(1, hexA(it.fill, 0));
        ctx.fillStyle = g;
        ctx.beginPath();
        ctx.arc(cx, cy, R, 0, Math.PI * 2);
        ctx.fill();
      }
      if (it.w >= 16 || it.h >= 16) {
        var g2 = ctx.createRadialGradient(cx - it.w * 0.16, cy - it.h * 0.18, 2, cx, cy, Math.max(it.w, it.h) * 0.55);
        g2.addColorStop(0, shade(it.fill, 85));
        g2.addColorStop(0.5, it.fill);
        g2.addColorStop(1, shade(it.fill, -28));
        ctx.fillStyle = g2;
      } else ctx.fillStyle = it.fill;
      ctx.beginPath();
      ctx.ellipse(cx, cy, Math.max(0.4, it.w / 2), Math.max(0.4, it.h / 2), 0, 0, Math.PI * 2);
      ctx.fill();
    });
  }
  function drawDoor(it) {
    withLocal(it, function () {
      traceArch(ctx, it.w, it.h, true);
      var g = ctx.createLinearGradient(0, 0, 0, it.h);
      g.addColorStop(0, shade(it.fill, 28));
      g.addColorStop(1, shade(it.fill, -12));
      ctx.fillStyle = g;
      ctx.fill();
    });
  }
  function drawFrame(it) {
    withLocal(it, function () {
      var sw = it.stroke || 14;
      ctx.lineJoin = "round";
      ctx.lineCap = "square";
      traceArch(ctx, it.w, it.h, false);
      ctx.lineWidth = sw;
      ctx.strokeStyle = it.fill || "#fff";
      ctx.stroke();
      var inset = sw * 0.62;
      ctx.translate(inset, inset * 0.3);
      traceArch(ctx, Math.max(8, it.w - inset * 2), Math.max(8, it.h - inset * 0.3), false);
      ctx.lineWidth = Math.max(1.2, sw * 0.11);
      ctx.strokeStyle = it.ink || "#e7c27a";
      ctx.stroke();
    });
  }
  function drawStar(it) {
    withLocal(it, function () {
      var cx = it.w / 2, cy = it.h / 2;
      var R = Math.min(it.w, it.h) / 2;
      var r = R * 0.42;
      ctx.beginPath();
      for (var n = 0; n < 10; n++) {
        var rad = n % 2 ? r : R;
        var a = -Math.PI / 2 + n * Math.PI / 5;
        var x = cx + Math.cos(a) * rad;
        var y = cy + Math.sin(a) * rad;
        if (n === 0) ctx.moveTo(x, y);
        else ctx.lineTo(x, y);
      }
      ctx.closePath();
      ctx.fillStyle = it.fill || "#f0c14e";
      ctx.fill();
    });
  }
  function drawBadge(it) {
    withLocal(it, function () {
      pathRound(ctx, 0, 0, it.w, it.h, Math.min(it.w, it.h) / 2);
      ctx.fillStyle = it.fill || "#f0c14e";
      ctx.fill();
      ctx.fillStyle = it.ink || "#1c2430";
      ctx.font = "700 " + Math.max(10, Math.floor(it.h * 0.28)) + "px " + SANS;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(it.text || "", it.w / 2, it.h / 2 + 0.5);
    });
  }
  function drawSprig(it) {
    withLocal(it, function () {
      ctx.translate(it.w / 2, it.h / 2);
      ctx.scale(it.w / 48, it.h / 72);
      ctx.translate(-24, -36);
      ctx.strokeStyle = it.fill;
      ctx.fillStyle = it.fill;
      ctx.lineWidth = 2;
      ctx.lineCap = "round";
      ctx.beginPath();
      ctx.moveTo(24, 68);
      ctx.quadraticCurveTo(26, 36, 22, 8);
      ctx.stroke();
      function leaf(x, y, rot, s) {
        ctx.save();
        ctx.translate(x, y);
        ctx.rotate(rot);
        ctx.scale(s, s);
        ctx.beginPath();
        ctx.moveTo(0, 8);
        ctx.quadraticCurveTo(14, 4, 0, -12);
        ctx.quadraticCurveTo(-14, 4, 0, 8);
        ctx.fill();
        ctx.restore();
      }
      leaf(16, 48, -0.9, 1);
      leaf(32, 32, 0.8, 0.9);
      leaf(14, 20, -0.55, 0.75);
    });
  }
  function drawText(it) {
    withLocal(it, function () {
      ctx.fillStyle = it.fill || "#111";
      ctx.font = fontOf(it);
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      var s = it.text || "";
      var track = it.track || 0;
      var cx = it.w / 2, cy = it.h / 2;
      if (track && s.length > 1) {
        var widths = [];
        var total = 0;
        for (var n = 0; n < s.length; n++) {
          var w = ctx.measureText(s.charAt(n)).width;
          widths.push(w);
          total += w;
        }
        total += track * (s.length - 1);
        var x = cx - total / 2;
        for (var n = 0; n < s.length; n++) {
          ctx.fillText(s.charAt(n), x + widths[n] / 2, cy);
          x += widths[n] + track;
        }
      } else ctx.fillText(s, cx, cy);
    });
  }
  function drawItem(it, t) {
    if (it.type === "rect") drawRect(it);
    else if (it.type === "ellipse") drawEllipse(it, t);
    else if (it.type === "text") drawText(it);
    else if (it.type === "door") drawDoor(it);
    else if (it.type === "frame") drawFrame(it);
    else if (it.type === "star") drawStar(it);
    else if (it.type === "badge") drawBadge(it);
    else if (it.type === "sprig") drawSprig(it);
  }
  function tick(x, y, sx, sy, color) {
    ctx.save();
    ctx.strokeStyle = color;
    ctx.lineWidth = 1.25;
    ctx.lineCap = "square";
    ctx.beginPath();
    ctx.moveTo(x, y);
    ctx.lineTo(x + 14 * sx, y);
    ctx.moveTo(x, y);
    ctx.lineTo(x, y + 14 * sy);
    ctx.stroke();
    ctx.restore();
  }
  function drawMarks() {
    var topDark = lum(doc.paper) < 0.5;
    var botDark = doc.band ? lum(doc.band) < 0.5 : topDark;
    var top = topDark ? "rgba(246,239,228,0.55)" : "rgba(28,36,48,0.38)";
    var bot = botDark ? "rgba(246,239,228,0.55)" : "rgba(28,36,48,0.38)";
    tick(16, 16, 1, 1, top);
    tick(DW - 16, 16, -1, 1, top);
    tick(16, DH - 16, 1, -1, bot);
    tick(DW - 16, DH - 16, -1, -1, bot);
    if (!doc.band) {
      ctx.strokeStyle = topDark ? "rgba(246,239,228,0.28)" : "rgba(28,36,48,0.16)";
      ctx.lineWidth = 1;
      ctx.strokeRect(22.5, 22.5, DW - 45, DH - 45);
    }
  }
  function grain() {
    if (!grainSrc) {
      grainSrc = document.createElement("canvas");
      grainSrc.width = 96;
      grainSrc.height = 96;
      var g = grainSrc.getContext("2d");
      var img = g.createImageData(96, 96);
      var d = img.data;
      var rr = rndFn(3);
      for (var n = 0; n < d.length; n += 4) {
        var v = 180 + ((rr() * 70) | 0);
        d[n] = d[n + 1] = d[n + 2] = v;
        d[n + 3] = 255;
      }
      g.putImageData(img, 0, 0);
    }
    if (grainCtx !== ctx) {
      grainPat = ctx.createPattern(grainSrc, "repeat");
      grainCtx = ctx;
    }
    return grainPat;
  }
  function corners(it) {
    var cx = it.x + it.w / 2, cy = it.y + it.h / 2;
    var c = Math.cos(it.rot || 0), s = Math.sin(it.rot || 0);
    var hw = it.w / 2, hh = it.h / 2;
    var loc = [[-hw, -hh], [hw, -hh], [hw, hh], [-hw, hh]];
    var out = [];
    for (var n = 0; n < 4; n++) {
      out.push({
        x: cx + loc[n][0] * c - loc[n][1] * s,
        y: cy + loc[n][0] * s + loc[n][1] * c
      });
    }
    return out;
  }
  function drawSelection(it) {
    var pts = corners(it);
    ctx.save();
    ctx.lineWidth = 1.5 / view.s;
    ctx.setLineDash([5 / view.s, 4 / view.s]);
    ctx.beginPath();
    ctx.moveTo(pts[0].x, pts[0].y);
    for (var n = 1; n < 4; n++) ctx.lineTo(pts[n].x, pts[n].y);
    ctx.closePath();
    ctx.strokeStyle = "rgba(0,0,0,0.45)";
    ctx.stroke();
    ctx.strokeStyle = "#fffaf3";
    ctx.stroke();
    ctx.setLineDash([]);
    var r = 6.5 / view.s;
    for (var n = 0; n < 4; n++) {
      ctx.beginPath();
      ctx.arc(pts[n].x, pts[n].y, r, 0, Math.PI * 2);
      ctx.fillStyle = "#fffaf3";
      ctx.fill();
      ctx.lineWidth = 1.25 / view.s;
      ctx.strokeStyle = "#1c2430";
      ctx.stroke();
    }
    ctx.restore();
  }
  function drawGuides() {
    ctx.save();
    ctx.strokeStyle = "rgba(226,90,42,0.9)";
    ctx.lineWidth = 1 / view.s;
    ctx.setLineDash([4 / view.s, 3 / view.s]);
    if (guides.v != null) {
      ctx.beginPath();
      ctx.moveTo(guides.v, 0);
      ctx.lineTo(guides.v, DH);
      ctx.stroke();
    }
    if (guides.h != null) {
      ctx.beginPath();
      ctx.moveTo(0, guides.h);
      ctx.lineTo(DW, guides.h);
      ctx.stroke();
    }
    ctx.restore();
  }
  function renderPoster(t, chrome) {
    var g = ctx.createLinearGradient(0, 0, 0, DH);
    g.addColorStop(0, doc.paper);
    g.addColorStop(1, doc.paper2 || doc.paper);
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, DW, DH);
    if (doc.band) {
      ctx.fillStyle = doc.band;
      ctx.fillRect(0, doc.bandY, DW, DH - doc.bandY);
    }
    for (var n = 0; n < doc.items.length; n++) drawItem(doc.items[n], t);
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, 0, DW, DH);
    ctx.clip();
    ctx.globalAlpha = 0.14;
    ctx.globalCompositeOperation = "overlay";
    var pat = grain();
    if (pat) {
      ctx.fillStyle = pat;
      ctx.fillRect(0, 0, DW, DH);
    }
    ctx.restore();
    drawMarks();
    ctx.strokeStyle = "rgba(40,24,12,0.35)";
    ctx.lineWidth = 1;
    ctx.strokeRect(0.5, 0.5, DW - 1, DH - 1);
    if (chrome) {
      drawGuides();
      if (sel >= 0 && doc.items[sel]) drawSelection(doc.items[sel]);
    }
  }

  function layout() {
    var vw = (stage && stage.clientWidth) || window.innerWidth || 390;
    var vh = (stage && stage.clientHeight) || window.innerHeight || 844;
    view.vw = vw;
    view.vh = vh;
    view.dpr = Math.min(window.devicePixelRatio || 1, 2);
    var padX = 14, padTop = 12, padBot = 32;
    var aw = Math.max(40, vw - padX * 2);
    var ah = Math.max(40, vh - padTop - padBot);
    view.s = Math.min(aw / DW, ah / DH);
    if (!(view.s > 0)) view.s = 0.01;
    var pw = DW * view.s;
    var ph = DH * view.s;
    view.ox = (vw - pw) / 2;
    view.oy = padTop + (ah - ph) / 2;
  }
  function inPoster(x, y) {
    var pw = DW * view.s, ph = DH * view.s;
    return x >= view.ox && x <= view.ox + pw && y >= view.oy && y <= view.oy + ph;
  }
  function drawTape(x, y, r) {
    ctx.save();
    ctx.translate(x, y);
    ctx.fillStyle = "rgba(90,50,20,0.12)";
    ctx.beginPath();
    ctx.ellipse(3, r * 0.45, r * 0.95, r * 0.32, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = "#e7c56a";
    ctx.beginPath();
    ctx.arc(0, 0, r, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = "#f4e2a6";
    ctx.beginPath();
    ctx.arc(0, 0, r * 0.52, 0, Math.PI * 2);
    ctx.fill();
    ctx.strokeStyle = "rgba(120,80,20,0.35)";
    ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.arc(0, 0, r * 0.76, 0.5, 2.4);
    ctx.stroke();
    ctx.restore();
  }
  function drawPencil(x, y, len) {
    ctx.save();
    ctx.translate(x, y);
    pathRound(ctx, 16, -5, len - 28, 10, 3);
    ctx.fillStyle = "#f0a03a";
    ctx.fill();
    pathRound(ctx, 0, -5, 16, 10, 3);
    ctx.fillStyle = "#e07a8a";
    ctx.fill();
    ctx.fillStyle = "#efe8dc";
    ctx.fillRect(14, -5, 5, 10);
    ctx.beginPath();
    ctx.moveTo(len - 18, -5);
    ctx.lineTo(len, 0);
    ctx.lineTo(len - 18, 5);
    ctx.closePath();
    ctx.fillStyle = "#f6efe4";
    ctx.fill();
    ctx.beginPath();
    ctx.moveTo(len - 7, -2.2);
    ctx.lineTo(len, 0);
    ctx.lineTo(len - 7, 2.2);
    ctx.closePath();
    ctx.fillStyle = "#2a241e";
    ctx.fill();
    ctx.restore();
  }
  function drawDesk(t) {
    var w = view.vw, h = view.vh;
    var g = ctx.createLinearGradient(0, 0, 0, h);
    g.addColorStop(0, "#f3ddb8");
    g.addColorStop(0.48, "#e4c08e");
    g.addColorStop(1, "#c99562");
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, w, h);
    var light = ctx.createRadialGradient(w * 0.15, 0, 8, w * 0.35, h * 0.15, w);
    light.addColorStop(0, "rgba(255,246,224,0.55)");
    light.addColorStop(1, "rgba(255,246,224,0)");
    ctx.fillStyle = light;
    ctx.fillRect(0, 0, w, h);
    var n;
    for (n = 0; n < knots.length; n++) {
      var kx = knots[n].x * w;
      var ky = knots[n].y * h;
      if (inPoster(kx, ky)) continue;
      ctx.fillStyle = "rgba(90,52,24," + knots[n].a + ")";
      ctx.beginPath();
      ctx.arc(kx, ky, knots[n].r, 0, Math.PI * 2);
      ctx.fill();
    }
    for (n = 0; n < motes.length; n++) {
      var my = (motes[n].y - t * 0.00001 * motes[n].v * 1000) % 1;
      if (my < 0) my += 1;
      var mx = motes[n].x * w + Math.sin(t * 0.00035 + n) * 7;
      var yy = my * h;
      if (inPoster(mx, yy)) continue;
      ctx.fillStyle = "rgba(255,248,230," + motes[n].a + ")";
      ctx.beginPath();
      ctx.arc(mx, yy, motes[n].r, 0, Math.PI * 2);
      ctx.fill();
    }
    if (view.oy > 58) drawTape(46, Math.min(40, view.oy * 0.42), 17);
    else if (view.ox > 52) drawTape(view.ox * 0.48, 78, 15);
  }
  function drawCredit() {
    ctx.save();
    ctx.font = "11px " + SANS;
    ctx.fillStyle = "rgba(62,40,24,0.78)";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText("idea after @shaongitbd (shaongitbd/doory);", view.vw / 2, view.vh - 20);
    ctx.fillText("clean-room implementation, no code copied", view.vw / 2, view.vh - 8);
    ctx.restore();
  }
  function draw(t) {
    layout();
    if (view.vw < 8 || view.vh < 8) return false;
    var dpr = view.dpr;
    var bw = Math.max(2, Math.round(view.vw * dpr));
    var bh = Math.max(2, Math.round(view.vh * dpr));
    if (cv.width !== bw || cv.height !== bh) {
      cv.width = bw;
      cv.height = bh;
      grainCtx = null;
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    drawDesk(t || 0);
    var pw = DW * view.s, ph = DH * view.s;
    ctx.save();
    ctx.fillStyle = "rgba(70,42,18,0.22)";
    ctx.beginPath();
    ctx.ellipse(view.ox + pw / 2, view.oy + ph - 2, pw * 0.4, Math.max(6, 8 * view.s), 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
    ctx.save();
    ctx.translate(view.ox, view.oy);
    ctx.scale(view.s, view.s);
    renderPoster(t || 0, true);
    ctx.restore();
    var pb = view.oy + ph;
    var gap = (view.vh - 32) - pb;
    if (gap > 36) drawPencil(view.vw / 2 - 78, pb + gap * 0.42, 150);
    drawCredit();
    return true;
  }

  function toD(cx, cy) {
    var b = cv.getBoundingClientRect();
    return {
      x: (cx - b.left - view.ox) / view.s,
      y: (cy - b.top - view.oy) / view.s
    };
  }
  function toLocal(it, x, y) {
    var cx = it.x + it.w / 2, cy = it.y + it.h / 2;
    var dx = x - cx, dy = y - cy;
    var c = Math.cos(-(it.rot || 0)), s = Math.sin(-(it.rot || 0));
    return { x: dx * c - dy * s + it.w / 2, y: dx * s + dy * c + it.h / 2 };
  }
  function inArchLocal(w, h, x, y, pad) {
    var x0 = -pad, y0 = -pad, w2 = w + pad * 2, h2 = h + pad;
    var lx = x - x0, ly = y - y0;
    if (lx < 0 || ly < 0 || lx > w2 || ly > h2) return false;
    var r = w2 / 2;
    if (ly >= r) return true;
    var dx = lx - r, dy = ly - r;
    return dx * dx + dy * dy <= r * r;
  }
  function hits(it, x, y) {
    var p = toLocal(it, x, y);
    if (it.type === "door") return inArchLocal(it.w, it.h, p.x, p.y, 0);
    if (it.type === "frame") {
      var sw = (it.stroke || 14) * 0.55 + 4;
      return inArchLocal(it.w, it.h, p.x, p.y, sw) && !inArchLocal(it.w, it.h, p.x, p.y, -sw * 0.35);
    }
    if (it.type === "ellipse" || it.type === "badge") {
      var nx = (p.x - it.w / 2) / (it.w / 2);
      var ny = (p.y - it.h / 2) / (it.h / 2);
      return nx * nx + ny * ny <= 1;
    }
    return p.x >= -6 && p.y >= -6 && p.x <= it.w + 6 && p.y <= it.h + 6;
  }
  function topHit(x, y) {
    for (var n = doc.items.length - 1; n >= 0; n--) {
      if (hits(doc.items[n], x, y)) return n;
    }
    return -1;
  }
  function hitHandle(it, x, y) {
    var pts = corners(it);
    var slop = 18 / view.s;
    for (var n = 0; n < 4; n++) {
      if (Math.hypot(x - pts[n].x, y - pts[n].y) <= slop) return n;
    }
    return -1;
  }
  function applyFromStart(it, start, k, rot) {
    var minK = 14 / Math.max(8, start.w);
    var maxK = (DW * 1.45) / Math.max(8, start.w);
    k = clamp(k, minK, maxK);
    var cx = start.x + start.w / 2;
    var cy = start.y + start.h / 2;
    it.w = start.w * k;
    it.h = Math.max(14, start.h * k);
    it.x = cx - it.w / 2;
    it.y = cy - it.h / 2;
    it.rot = rot || 0;
    if (start.size) it.size = clamp(start.size * k, 8, 220);
    if (start.stroke) it.stroke = start.stroke * k;
    if (start.track) it.track = start.track * k;
    var q = Math.PI / 2;
    var snapped = Math.round(it.rot / q) * q;
    if (Math.abs(it.rot - snapped) < 0.07) it.rot = snapped;
  }
  function applyMove(it, start, dx, dy) {
    it.x = start.x + dx;
    it.y = start.y + dy;
    guides.v = null;
    guides.h = null;
    var cx = it.x + it.w / 2;
    var cy = it.y + it.h / 2;
    if (Math.abs(cx - DW / 2) < 7) {
      it.x += DW / 2 - cx;
      guides.v = DW / 2;
      cx = DW / 2;
    }
    if (Math.abs(cy - DH / 2) < 7) {
      it.y += DH / 2 - cy;
      guides.h = DH / 2;
      cy = DH / 2;
    }
    if (doc.bandY && Math.abs(it.y - doc.bandY) < 6) {
      it.y = doc.bandY;
      guides.h = doc.bandY;
    }
    for (var n = 0; n < doc.items.length; n++) {
      var o = doc.items[n];
      if (o === it) continue;
      var ocx = o.x + o.w / 2;
      if (Math.abs(cx - ocx) < 6) {
        it.x += ocx - cx;
        guides.v = ocx;
        break;
      }
    }
  }
  function pinchInfo() {
    var ks = Object.keys(ptrs);
    if (ks.length < 2) return null;
    var a = ptrs[ks[0]], b = ptrs[ks[1]];
    var dx = b.x - a.x, dy = b.y - a.y;
    return {
      dist: Math.hypot(dx, dy) || 1,
      ang: Math.atan2(dy, dx),
      mx: (a.x + b.x) / 2,
      my: (a.y + b.y) / 2
    };
  }
  function beginPinch() {
    var info = pinchInfo();
    if (!info) return;
    var p = toD(info.mx, info.my);
    if (sel < 0) {
      var id = topHit(p.x, p.y);
      if (id >= 0) sel = id;
    }
    if (sel < 0) {
      gesture = { mode: "none", moved: false };
      return;
    }
    gesture = {
      mode: "pinch",
      id: sel,
      moved: false,
      snapped: false,
      start: clone(doc.items[sel]),
      dist: info.dist,
      ang: info.ang
    };
    pinching = true;
    syncPanel();
  }
  function onDown(e) {
    if (e.button != null && e.button !== 0) return;
    ptrs[e.pointerId] = { x: e.clientX, y: e.clientY };
    try { cv.setPointerCapture(e.pointerId); } catch (err) {}
    var keys = Object.keys(ptrs);
    if (keys.length >= 2) {
      beginPinch();
    } else {
      var p = toD(e.clientX, e.clientY);
      var handle = -1;
      if (sel >= 0 && doc.items[sel]) handle = hitHandle(doc.items[sel], p.x, p.y);
      var id = handle >= 0 ? sel : topHit(p.x, p.y);
      gesture = {
        mode: handle >= 0 ? "scale" : id >= 0 ? "move" : "none",
        id: id,
        moved: false,
        snapped: false,
        selBefore: sel,
        x0: e.clientX,
        y0: e.clientY,
        sx: p.x,
        sy: p.y,
        start: id >= 0 ? clone(doc.items[id]) : null
      };
      if (id >= 0) {
        sel = id;
        syncPanel();
      }
      pinching = false;
    }
    if (e.cancelable) e.preventDefault();
  }
  function onMove(e) {
    if (!ptrs[e.pointerId]) return;
    ptrs[e.pointerId].x = e.clientX;
    ptrs[e.pointerId].y = e.clientY;
    if (!gesture) return;
    if (gesture.mode === "pinch" || Object.keys(ptrs).length >= 2) {
      var info = pinchInfo();
      if (!info || gesture.mode !== "pinch" || gesture.id < 0) return;
      if (!gesture.snapped) {
        snapshot();
        gesture.snapped = true;
        gesture.moved = true;
      }
      var k = info.dist / gesture.dist;
      var rot = (gesture.start.rot || 0) + (info.ang - gesture.ang);
      applyFromStart(doc.items[gesture.id], gesture.start, k, rot);
      if (e.cancelable) e.preventDefault();
      return;
    }
    if (gesture.mode !== "move" && gesture.mode !== "scale") return;
    var p = toD(e.clientX, e.clientY);
    var screenD = Math.hypot(e.clientX - gesture.x0, e.clientY - gesture.y0);
    if (!gesture.moved && screenD > 4) {
      gesture.moved = true;
      if (!gesture.snapped) {
        snapshot();
        gesture.snapped = true;
      }
    }
    if (!gesture.moved || gesture.id < 0) return;
    if (gesture.mode === "move") applyMove(doc.items[gesture.id], gesture.start, p.x - gesture.sx, p.y - gesture.sy);
    else {
      var st = gesture.start;
      var cx = st.x + st.w / 2, cy = st.y + st.h / 2;
      var d0 = Math.hypot(gesture.sx - cx, gesture.sy - cy) || 1;
      var d1 = Math.hypot(p.x - cx, p.y - cy) || 1;
      applyFromStart(doc.items[gesture.id], st, d1 / d0, st.rot || 0);
    }
    if (e.cancelable) e.preventDefault();
  }
  function onUp(e) {
    if (!ptrs[e.pointerId]) return;
    delete ptrs[e.pointerId];
    var left = Object.keys(ptrs).length;
    if (left > 0) {
      if (left >= 2) beginPinch();
      else pinching = false;
      return;
    }
    pinching = false;
    if (gesture && !gesture.moved && gesture.mode === "none") {
      sel = -1;
      syncPanel();
    } else if (gesture && !gesture.moved && gesture.mode === "move" && gesture.selBefore === gesture.id) {
      var it = doc.items[gesture.id];
      if (it && (it.type === "text" || it.type === "badge") && document.documentElement.classList.contains("gb-ui-open")) {
        words.focus();
      }
    }
    if (gesture && gesture.moved) {
      guides.v = null;
      guides.h = null;
      save();
      blip(gesture.mode === "pinch" || gesture.mode === "scale" ? 640 : 480);
    }
    gesture = null;
  }

  function labelOf(it) {
    if (!it) return "Page";
    if (it.type === "text" || it.type === "badge") return it.text || "Text";
    if (it.type === "door") return "Door";
    if (it.type === "frame") return "Frame";
    if (it.type === "star") return "Star";
    if (it.type === "sprig") return "Sprig";
    if (it.type === "ellipse") return it.glow ? "Lantern" : "Circle";
    return "Block";
  }
  function syncPanel() {
    var it = sel >= 0 ? doc.items[sel] : null;
    var name = document.getElementById("selname");
    if (name) name.textContent = it ? labelOf(it) : (doc.name || "Page");
    if (it && (it.type === "text" || it.type === "badge")) {
      words.disabled = false;
      if (document.activeElement !== words) words.value = it.text || "";
    } else {
      words.disabled = true;
      if (document.activeElement !== words) words.value = "";
    }
    var col = (it && it.fill ? it.fill : doc.paper).toLowerCase();
    var nodes = panel.querySelectorAll("button");
    for (var n = 0; n < nodes.length; n++) {
      var c = nodes[n].getAttribute("data-color");
      if (c) nodes[n].classList.toggle("on", c.toLowerCase() === col);
      var act = nodes[n].getAttribute("data-act");
      if (act === "blank" || act === "lantern" || act === "invite") {
        nodes[n].classList.toggle("onact", act === doc.kind);
      }
    }
  }
  function inkForPage() {
    var base = doc.band || doc.paper;
    return lum(base) > 0.62 ? "#1c2430" : "#f6efe4";
  }
  function nextAccent() {
    var list = ["#e25a2a", "#f0c14e", "#2f6b4f", "#3d6f8f", "#d4526e"];
    var c = list[accentI % list.length];
    accentI++;
    return c;
  }
  function selectLast() {
    sel = doc.items.length - 1;
    save();
    syncPanel();
  }
  function addText() {
    snapshot();
    var it = E({
      type: "text", text: "New line", size: 32, weight: 700, font: SERIF,
      fill: inkForPage(), x: 0, y: 0, w: 20, h: 20, track: 0
    });
    fitLine(it, DW - 48);
    var cy = doc.band ? (doc.bandY + DH) / 2 : DH / 2;
    place(it, DW / 2, cy);
    doc.items.push(it);
    selectLast();
    blip(620);
  }
  function addShape(type) {
    snapshot();
    var it = E({ type: type, x: 0, y: 0, w: 84, h: 84, fill: nextAccent(), r: type === "rect" ? 14 : 0 });
    if (type === "star") { it.w = 72; it.h = 72; }
    var cy = doc.band ? (doc.bandY + DH) / 2 : DH / 2;
    it.x = DW / 2 - it.w / 2 + (accentI % 3) * 10;
    it.y = cy - it.h / 2;
    doc.items.push(it);
    selectLast();
    blip(600);
  }
  function doColor(col) {
    snapshot();
    if (sel < 0 || !doc.items[sel]) {
      doc.paper = col;
      doc.paper2 = shade(col, -36);
    } else {
      var it = doc.items[sel];
      it.fill = col;
      if (it.type === "badge") it.ink = lum(col) > 0.62 ? "#1c2430" : "#f6efe4";
    }
    save();
    syncPanel();
    blip(700);
  }
  function applyDoc(next) {
    snapshot();
    doc = next;
    sel = -1;
    guides.v = null;
    guides.h = null;
    reindex();
    save();
    syncPanel();
    blip(440);
  }
  function doAct(act) {
    var it;
    if (act === "text") return addText();
    if (act === "ellipse" || act === "rect" || act === "star") return addShape(act);
    if (act === "blank") return applyDoc(seedBlank());
    if (act === "lantern") return applyDoc(seedLantern());
    if (act === "invite") return applyDoc(seedInvite());
    if (act === "undo") {
      if (!hist.length) return;
      doc = JSON.parse(hist.pop());
      sel = -1;
      reindex();
      save();
      syncPanel();
      blip(320);
      return;
    }
    if (act === "png") return exportPNG();
    if (sel < 0 || !doc.items[sel]) return;
    if (act === "smaller" || act === "larger") {
      snapshot();
      applyFromStart(doc.items[sel], clone(doc.items[sel]), act === "larger" ? 1.12 : 0.88, doc.items[sel].rot || 0);
      save();
      syncPanel();
      blip(560);
      return;
    }
    if (act === "dup") {
      snapshot();
      it = clone(doc.items[sel]);
      it.id = nid++;
      it.x += 18;
      it.y += 18;
      doc.items.push(it);
      selectLast();
      blip(560);
      return;
    }
    if (act === "del") {
      snapshot();
      doc.items.splice(sel, 1);
      sel = -1;
      save();
      syncPanel();
      blip(300);
      return;
    }
    if (act === "front" || act === "back") {
      if (act === "front" && sel === doc.items.length - 1) return;
      if (act === "back" && sel === 0) return;
      snapshot();
      it = doc.items.splice(sel, 1)[0];
      if (act === "front") {
        doc.items.push(it);
        sel = doc.items.length - 1;
      } else {
        doc.items.unshift(it);
        sel = 0;
      }
      save();
      syncPanel();
      blip(520);
    }
  }
  function exportPNG() {
    var oc = document.createElement("canvas");
    oc.width = DW;
    oc.height = DH;
    var c = oc.getContext("2d");
    var prev = ctx;
    ctx = c;
    grainCtx = null;
    renderPoster(0, false);
    ctx = prev;
    grainCtx = null;
    var a = document.createElement("a");
    a.href = oc.toDataURL("image/png");
    a.download = "doory.png";
    document.body.appendChild(a);
    a.click();
    a.remove();
    blip(860);
  }
  function blip(freq) {
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      if (!blip.ac) blip.ac = new AC();
      var ac = blip.ac;
      if (ac.state === "suspended") ac.resume();
      var o = ac.createOscillator();
      var g = ac.createGain();
      o.type = "sine";
      o.frequency.value = freq || 520;
      g.gain.setValueAtTime(0.0001, ac.currentTime);
      g.gain.exponentialRampToValueAtTime(0.03, ac.currentTime + 0.012);
      g.gain.exponentialRampToValueAtTime(0.0001, ac.currentTime + 0.08);
      o.connect(g);
      g.connect(ac.destination);
      o.start();
      o.stop(ac.currentTime + 0.09);
    } catch (e) {}
  }

  function eatTouch(e) {
    if (e.type === "touchmove" && e.cancelable) e.preventDefault();
  }
  cv.addEventListener("pointerdown", onDown, { passive: false });
  cv.addEventListener("pointermove", onMove, { passive: false });
  cv.addEventListener("pointerup", onUp);
  cv.addEventListener("pointercancel", onUp);
  window.addEventListener("pointerup", onUp);
  window.addEventListener("pointercancel", onUp);
  cv.addEventListener("touchstart", eatTouch, { passive: false });
  cv.addEventListener("touchmove", eatTouch, { passive: false });
  cv.addEventListener("touchend", eatTouch, { passive: false });
  cv.addEventListener("touchcancel", eatTouch, { passive: false });
  cv.addEventListener("contextmenu", function (e) { e.preventDefault(); });
  cv.addEventListener("wheel", function (e) {
    if (!e.ctrlKey || pinching) return;
    e.preventDefault();
    var p = toD(e.clientX, e.clientY);
    if (sel < 0) {
      var id = topHit(p.x, p.y);
      if (id < 0) return;
      sel = id;
      syncPanel();
    }
    if (!wheelSnap) {
      snapshot();
      wheelSnap = true;
    }
    clearTimeout(wheelT);
    wheelT = setTimeout(function () { wheelSnap = false; save(); }, 180);
    var it = doc.items[sel];
    var k = Math.exp(-e.deltaY * 0.006);
    applyFromStart(it, clone(it), k, it.rot || 0);
  }, { passive: false });

  function stopBubble(e) { e.stopPropagation(); }
  ["pointerdown", "pointermove", "pointerup", "pointercancel", "touchstart", "touchmove", "touchend", "mousedown", "mouseup", "wheel", "click"].forEach(function (n) {
    panel.addEventListener(n, stopBubble);
  });
  panel.addEventListener("click", function (e) {
    var t = e.target && e.target.closest ? e.target.closest("button") : null;
    if (!t || !panel.contains(t)) return;
    var col = t.getAttribute("data-color");
    if (col) { doColor(col); return; }
    var act = t.getAttribute("data-act");
    if (act) doAct(act);
  });
  words.addEventListener("focus", function () {
    if (sel < 0) return;
    snapshot();
  });
  words.addEventListener("input", function () {
    if (sel < 0) return;
    var it = doc.items[sel];
    if (!it || (it.type !== "text" && it.type !== "badge")) return;
    it.text = words.value;
    if (it.type === "text") measure(it);
    syncPanel();
    saveSoon();
  });

  var sw = document.getElementById("swatches");
  for (i = 0; i < COLORS.length; i++) {
    var b = document.createElement("button");
    b.type = "button";
    b.setAttribute("data-color", COLORS[i]);
    b.style.background = COLORS[i];
    b.setAttribute("aria-label", "Color");
    sw.appendChild(b);
  }

  function poke() {
    if (readySent) return;
    if (!window.__gbSandbox || typeof window.__gbSandbox.ready !== "function") return;
    readySent = true;
    window.__gbSandbox.ready();
  }
  function frame(t) {
    requestAnimationFrame(frame);
    if (draw(t)) poke();
  }
  function localToggle() {
    if (window.__gbSandbox) return;
    if (document.getElementById("door-toggle") || document.getElementById("gb-ui-toggle")) return;
    var b = document.createElement("button");
    b.id = "door-toggle";
    b.type = "button";
    b.setAttribute("aria-label", "Show tools");
    b.textContent = "\u2699";
    b.addEventListener("click", function (e) {
      e.stopPropagation();
      var on = document.documentElement.classList.toggle("gb-ui-open");
      b.setAttribute("aria-expanded", on ? "true" : "false");
    });
    ["pointerdown", "pointerup", "touchstart", "touchend", "mousedown", "mouseup"].forEach(function (n) {
      b.addEventListener(n, function (e) { e.stopPropagation(); });
    });
    document.body.appendChild(b);
  }

  boot();
  syncPanel();
  if (draw(0)) poke();
  requestAnimationFrame(frame);
  localToggle();
  window.addEventListener("resize", function () { draw(performance.now()); });
})();
