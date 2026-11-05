/*
 * app.js  -  user interface for the graph coloring solver.
 * The algorithm itself lives in solver.js (GraphSolver.solve).
 *
 * Data flow: text box -> parse() -> model {names, edges} -> GraphSolver.solve() -> render.
 * Edits made on the graph change the model, which is written back into the text box.
 */
(function () {
  'use strict';

  var MAXV = 120;
  var SIZE = 520;
  var PALETTE = ['#2563c9', '#d9780f', '#a8318a', '#1d8a5a', '#c13b3b', '#6a4fc2', '#0f8aa0', '#8a7a10', '#546478', '#b5581e'];
  function colorFor(i) {
    return i < PALETTE.length ? PALETTE[i] : 'hsl(' + Math.round((i * 137.508) % 360) + ' 55% 40%)';
  }

  /* ---------- example problems ---------- */
  var PRESETS = {
    fish: {
      label: 'Fish tanks (10 exotic fish)', noun: 'Tank', layout: 'circle',
      text: [
        '# Fish that cannot be in the same tank',
        'F1: F2, F3, F4, F5, F10',
        'F2: F1, F3, F6',
        'F3: F1, F2, F4',
        'F4: F1, F3, F5',
        'F5: F1, F4, F9',
        'F6: F2, F7, F10',
        'F7: F6, F8, F10',
        'F8: F7, F9, F10',
        'F9: F5, F8, F10',
        'F10: F1, F6, F7, F8, F9'
      ].join('\n')
    },
    traffic: {
      label: 'Traffic light phases (lanes L1 to L7)', noun: 'Phase', layout: 'force',
      text: [
        '# Two lanes conflict when their paths cross, read from Figure 14.10.',
        '# Lanes in the same phase get a green light together.',
        'L1: L3, L4, L6',
        'L2: L3, L4',
        'L3: L1, L2',
        'L4: L1, L2, L6',
        'L5:',
        'L6: L1, L4',
        'L7:'
      ].join('\n')
    },
    australia: {
      label: 'Map of Australia (neighboring states)', noun: 'Color', layout: 'force',
      text: [
        '# States that share a border need different colors',
        'WA: NT, SA',
        'NT: WA, SA, QLD',
        'SA: WA, NT, QLD, NSW, VIC',
        'QLD: NT, SA, NSW',
        'NSW: QLD, SA, VIC',
        'VIC: SA, NSW',
        'TAS:'
      ].join('\n')
    },
    petersen: {
      label: 'Petersen graph', noun: 'Color', layout: 'force',
      text: [
        '# outer ring', 'A-B', 'B-C', 'C-D', 'D-E', 'E-A',
        '# spokes', 'A-F', 'B-G', 'C-H', 'D-I', 'E-J',
        '# inner star', 'F-H', 'H-J', 'J-G', 'G-I', 'I-F'
      ].join('\n')
    },
    wheel: {
      label: 'Wheel with 5 spokes', noun: 'Color', layout: 'force',
      text: ['Hub: R1, R2, R3, R4, R5', 'R1-R2', 'R2-R3', 'R3-R4', 'R4-R5', 'R5-R1'].join('\n')
    },
    k5: {
      label: 'Five items that all conflict', noun: 'Slot', layout: 'circle',
      text: ['# Everyone conflicts with everyone, so every item needs its own slot', 'A: B, C, D, E', 'B: C, D, E', 'C: D, E', 'D: E'].join('\n')
    }
  };

  /* ---------- state ---------- */
  var $ = function (id) { return document.getElementById(id); };
  var svg = $('graph'), src = $('src');
  var model = { names: [], edges: [], warnings: [] };
  var pos = {};
  var result = null;
  var revealed = new Set();
  var selected = null;
  var editMode = false;
  var timer = null, typing = null;
  var reduceMotion = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
  function noun() { return ($('noun').value.trim() || 'Group'); }
  function plural(word, k) { return word.toLowerCase() + (k === 1 ? '' : 's'); }
  function list(arr) {
    if (arr.length <= 1) return arr.join('');
    return arr.slice(0, -1).join(', ') + ' and ' + arr[arr.length - 1];
  }

  /* ---------- parsing ---------- */
  function parse(text) {
    var names = [], index = {}, seen = {}, edges = [], warnings = [], rows = [];
    function id(nm) {
      if (!Object.prototype.hasOwnProperty.call(index, nm)) { index[nm] = names.length; names.push(nm); }
      return index[nm];
    }
    text.split(/\r?\n/).forEach(function (raw, ln) {
      var line = raw.replace(/(#|\/\/).*$/, '').trim();
      if (!line) return;
      var head, tails;
      if (line.indexOf(':') >= 0) {
        var p = line.split(':');
        head = p[0].trim();
        tails = p.slice(1).join(' ').split(/[\s,;]+/).filter(Boolean);
        if (!head || /[\s,;]/.test(head)) { warnings.push('Line ' + (ln + 1) + ': put one name before the colon.'); return; }
      } else {
        var toks = line.split(/\s*(?:<->|->|--|—|–|-|,|;)\s*|\s+/).filter(Boolean);
        head = toks[0]; tails = toks.slice(1);
      }
      rows.push({ head: head, tails: tails, ln: ln + 1 });
    });
    rows.forEach(function (r) { id(r.head); });
    rows.forEach(function (r) {
      r.tails.forEach(function (t) {
        if (t === r.head) { warnings.push('Line ' + r.ln + ': ' + t + ' cannot conflict with itself, so it was ignored.'); return; }
        var a = id(r.head), b = id(t), lo = Math.min(a, b), hi = Math.max(a, b), k = lo + '-' + hi;
        if (!seen[k]) { seen[k] = 1; edges.push([lo, hi]); }
      });
    });
    if (names.length > MAXV) {
      warnings.push('That is ' + names.length + ' items. The limit is ' + MAXV + '.');
      return { names: [], edges: [], warnings: warnings };
    }
    return { names: names, edges: edges, warnings: warnings };
  }

  function serialize(names, edges) {
    var adj = names.map(function () { return []; });
    edges.forEach(function (e) { adj[e[0]].push(e[1]); adj[e[1]].push(e[0]); });
    return names.map(function (nm, i) {
      adj[i].sort(function (a, b) { return a - b; });
      return nm + ':' + (adj[i].length ? ' ' + adj[i].map(function (j) { return names[j]; }).join(', ') : '');
    }).join('\n');
  }

  /* ---------- layout ---------- */
  function circleLayout(n) {
    var out = [];
    for (var i = 0; i < n; i++) {
      var a = -Math.PI / 2 + i * 2 * Math.PI / n;
      out.push({ x: SIZE / 2 + 195 * Math.cos(a), y: SIZE / 2 + 195 * Math.sin(a) });
    }
    return out;
  }
  function forceLayout(n, edges) {
    var P = circleLayout(n), i, j, it, d, f, dx, dy;
    if (n < 3) return P;
    P.forEach(function (p, k) { p.x += Math.sin(k * 12.9898) * 14; p.y += Math.cos(k * 78.233) * 14; });
    var W = 440, K = Math.sqrt(W * W / n) * 0.9, temp = W / 8;
    for (it = 0; it < 320; it++) {
      var DX = new Array(n).fill(0), DY = new Array(n).fill(0);
      for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) {
        dx = P[i].x - P[j].x; dy = P[i].y - P[j].y; d = Math.sqrt(dx * dx + dy * dy) || 0.01;
        f = K * K / d; DX[i] += dx / d * f; DY[i] += dy / d * f; DX[j] -= dx / d * f; DY[j] -= dy / d * f;
      }
      edges.forEach(function (e) {
        var a = e[0], b = e[1], ex = P[a].x - P[b].x, ey = P[a].y - P[b].y, ed = Math.sqrt(ex * ex + ey * ey) || 0.01, ef = ed * ed / K;
        DX[a] -= ex / ed * ef; DY[a] -= ey / ed * ef; DX[b] += ex / ed * ef; DY[b] += ey / ed * ef;
      });
      for (i = 0; i < n; i++) {
        DX[i] -= (P[i].x - SIZE / 2) * 0.6; DY[i] -= (P[i].y - SIZE / 2) * 0.6;
        d = Math.sqrt(DX[i] * DX[i] + DY[i] * DY[i]) || 0.01;
        P[i].x += DX[i] / d * Math.min(d, temp); P[i].y += DY[i] / d * Math.min(d, temp);
      }
      temp *= 0.985;
    }
    var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    P.forEach(function (p) { minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x); minY = Math.min(minY, p.y); maxY = Math.max(maxY, p.y); });
    var s = Math.min(430 / Math.max(maxX - minX, 1), 430 / Math.max(maxY - minY, 1));
    return P.map(function (p) { return { x: SIZE / 2 + (p.x - (minX + maxX) / 2) * s, y: SIZE / 2 + (p.y - (minY + maxY) / 2) * s }; });
  }
  function layoutAll(kind) {
    var P = kind === 'force' ? forceLayout(model.names.length, model.edges) : circleLayout(model.names.length);
    pos = {};
    model.names.forEach(function (nm, i) { pos[nm] = P[i]; });
  }

  /* ---------- applying a problem ---------- */
  function applyText(text, opts) {
    opts = opts || {};
    model = parse(text);
    var warn = $('warn');
    warn.innerHTML = model.warnings.map(function (w) { return '<li>' + esc(w) + '</li>'; }).join('');

    var kept = {}, fresh = 0;
    model.names.forEach(function (nm, i) {
      if (pos[nm]) kept[nm] = pos[nm];
      else { fresh++; }
    });
    pos = kept;
    if (opts.layout || Object.keys(kept).length === 0) {
      layoutAll(opts.layout || 'circle');
    } else if (fresh) {
      model.names.forEach(function (nm, i) {
        if (!pos[nm]) pos[nm] = { x: 120 + ((i * 97) % 280), y: 120 + ((i * 53) % 280) };
      });
    }
    if (selected !== null && model.names.indexOf(selected) < 0) selected = null;

    stopTimer();
    result = model.names.length ? GraphSolver.solve(model.names.length, model.edges, { timeLimitMs: 1500 }) : null;
    revealed = new Set();
    if (opts.animate && result && !reduceMotion) { startReveal(); return; }
    if (result) for (var i = 0; i < model.names.length; i++) revealed.add(i);
    renderAll();
  }

  function commit(names, edges, opts) {
    src.value = serialize(names, edges);
    applyText(src.value, opts);
  }

  function stopTimer() { if (timer) { clearInterval(timer); timer = null; } }
  function startReveal() {
    stopTimer();
    var n = model.names.length, deg = model.names.map(function () { return 0; });
    model.edges.forEach(function (e) { deg[e[0]]++; deg[e[1]]++; });
    var order = [];
    for (var i = 0; i < n; i++) order.push(i);
    order.sort(function (a, b) { return deg[b] - deg[a] || a - b; });
    revealed = new Set();
    renderAll();
    var step = 0, delay = Math.max(90, Math.min(320, 2600 / n));
    timer = setInterval(function () {
      revealed.add(order[step++]);
      renderAll();
      if (step >= n) stopTimer();
    }, delay);
  }

  /* ---------- rendering ---------- */
  function adjacency() {
    var A = model.names.map(function () { return []; });
    model.edges.forEach(function (e) { A[e[0]].push(e[1]); A[e[1]].push(e[0]); });
    A.forEach(function (l) { l.sort(function (a, b) { return a - b; }); });
    return A;
  }
  function colorOf(i) { return result && revealed.has(i) ? result.colors[i] : -1; }
  function nodeRadius(n) { return n <= 12 ? 26 : n <= 25 ? 20 : n <= 50 ? 14 : 10; }

  function renderGraph() {
    var n = model.names.length;
    if (!n) {
      svg.innerHTML = '<text class="empty-note" x="260" y="250">Nothing to color yet.</text><text class="empty-note" x="260" y="276">Type items on the left, or turn on Edit and click here.</text>';
      return;
    }
    var r = nodeRadius(n), A = adjacency(), si = selected === null ? -1 : model.names.indexOf(selected);
    var hot = {};
    if (si >= 0) A[si].forEach(function (o) { hot[Math.min(si, o) + '-' + Math.max(si, o)] = 1; });
    var h = '';
    model.edges.forEach(function (e) {
      var a = pos[model.names[e[0]]], b = pos[model.names[e[1]]];
      h += '<line class="edge' + (hot[e[0] + '-' + e[1]] ? ' hot' : '') + '" x1="' + a.x.toFixed(1) + '" y1="' + a.y.toFixed(1) + '" x2="' + b.x.toFixed(1) + '" y2="' + b.y.toFixed(1) + '"/>';
    });
    model.names.forEach(function (nm, i) {
      var p = pos[nm], c = colorOf(i), isSel = i === si;
      var fill = c >= 0 ? colorFor(c) : 'var(--node-idle)';
      var txt = c >= 0 ? '#fff' : 'var(--ink)';
      var ring = isSel ? 'var(--accent)' : (c >= 0 ? 'var(--surface)' : 'var(--muted)');
      var fs = Math.max(8, Math.min(16, r * 1.7 / Math.max(1.8, nm.length * 0.62)));
      h += '<g data-i="' + i + '" tabindex="0" role="button" aria-label="' + esc(nm) + (c >= 0 ? ', ' + esc(noun()) + ' ' + (c + 1) : '') + '">' +
        '<title>' + esc(nm) + '</title>' +
        '<circle cx="' + p.x.toFixed(1) + '" cy="' + p.y.toFixed(1) + '" r="' + (isSel ? r + 3 : r) + '" fill="' + fill + '" stroke="' + ring + '" stroke-width="' + (isSel ? 4 : 2.5) + '"/>' +
        '<text class="node-label" x="' + p.x.toFixed(1) + '" y="' + (p.y + fs * 0.35).toFixed(1) + '" font-size="' + fs.toFixed(1) + '" fill="' + txt + '">' + esc(nm) + '</text></g>';
    });
    svg.innerHTML = h;
  }

  function renderAnswer() {
    var word = noun(), n = model.names.length;
    if (!result) {
      $('big').textContent = '-'; $('lbl').textContent = ''; $('why').textContent = 'Add at least one item to see the answer.';
      $('status').textContent = ''; $('tanks').innerHTML = '';
      $('replay').disabled = true; $('copy').disabled = true;
      return;
    }
    $('replay').disabled = false; $('copy').disabled = false;
    var k = result.k, names = model.names, why;
    $('big').textContent = k;
    $('lbl').textContent = plural(word, k) + (result.proven ? '' : ' (best found)');
    var cl = result.clique.map(function (i) { return '<b>' + esc(names[i]) + '</b>'; });
    if (!result.proven) {
      why = 'The search stopped after ' + (result.ms / 1000).toFixed(1) + ' seconds. ' + k + ' ' + plural(word, k) + ' works, and at least ' + result.lowerBound + ' are needed, so the true minimum is between ' + result.lowerBound + ' and ' + k + '.';
    } else if (k === 1) {
      why = 'No two items conflict, so one ' + word.toLowerCase() + ' is enough.';
    } else if (result.proof === 'clique') {
      why = list(cl) + (cl.length === 2 ? ' conflict' : ' all conflict with each other') + ', so they need ' + k + ' separate ' + plural(word, k) + '. A split into ' + k + ' exists, so ' + k + ' is the minimum.';
    } else {
      why = 'Every way of using ' + (k - 1) + ' ' + plural(word, k - 1) + ' was checked and none avoids all conflicts. A split into ' + k + ' exists, so ' + k + ' is the minimum.';
    }
    $('why').innerHTML = why;

    var bad = 0;
    model.edges.forEach(function (e) { if (result.colors[e[0]] === result.colors[e[1]]) bad++; });
    $('status').textContent = revealed.size < n
      ? 'Placing items: ' + revealed.size + ' of ' + n
      : 'Check: ' + bad + ' conflicting pairs share a ' + word.toLowerCase() + '. ' + n + ' items, ' + result.edgeCount + ' conflicts, most conflicts on one item: ' + result.maxDegree + '. Search: ' + result.nodes + ' steps, ' + result.ms + ' ms.';

    var h = '';
    for (var c = 0; c < k; c++) {
      var members = [];
      names.forEach(function (nm, i) { if (colorOf(i) === c) members.push(nm); });
      h += '<div class="tank" style="--tc:' + colorFor(c) + '"><h3>' + esc(word) + ' ' + (c + 1) + '<span>' + members.length + '</span></h3><div class="fishes">' +
        members.map(function (m) { return '<span class="chip">' + esc(m) + '</span>'; }).join('') + '</div></div>';
    }
    $('tanks').innerHTML = h;
  }

  function renderSel() {
    var el = $('sel'), si = selected === null ? -1 : model.names.indexOf(selected);
    $('del').disabled = si < 0;
    if (si < 0) { el.textContent = model.names.length ? 'Select an item on the graph to see what it conflicts with.' : ''; return; }
    var A = adjacency(), c = result ? result.colors[si] : -1;
    var others = A[si].map(function (j) { return model.names[j]; });
    el.innerHTML = '<b>' + esc(selected) + '</b>' + (c >= 0 && revealed.has(si) ? ' is in ' + esc(noun()) + ' ' + (c + 1) + ' and' : '') +
      ' conflicts with ' + (others.length ? esc(list(others)) : 'nothing') + '.';
  }

  function renderHint() {
    $('hint').textContent = editMode
      ? 'Edit is on. Click empty space to add an item. Click one item, then another, to add or remove a conflict between them.'
      : 'Each line joins two items that cannot share a ' + noun().toLowerCase() + '. Drag an item to move it, or select one to see its conflicts.';
  }

  function renderAll() { renderGraph(); renderAnswer(); renderSel(); renderHint(); }

  /* ---------- graph editing and dragging ---------- */
  var drag = null;
  function svgPoint(e) {
    var pt = svg.createSVGPoint(); pt.x = e.clientX; pt.y = e.clientY;
    return pt.matrixTransform(svg.getScreenCTM().inverse());
  }
  function nextName() {
    var m = /^(\D*)\d+$/.exec(model.names[model.names.length - 1] || ''), prefix = m ? m[1] : 'V', k = model.names.length + 1;
    while (model.names.indexOf(prefix + k) >= 0) k++;
    return prefix + k;
  }
  function toggleEdge(an, bn) {
    var a = model.names.indexOf(an), b = model.names.indexOf(bn), lo = Math.min(a, b), hi = Math.max(a, b), found = false;
    var edges = model.edges.filter(function (e) { if (e[0] === lo && e[1] === hi) { found = true; return false; } return true; });
    if (!found) edges.push([lo, hi]);
    commit(model.names.slice(), edges, {});
  }
  function addVertex(x, y) {
    if (model.names.length >= MAXV) return;
    var nm = nextName(), names = model.names.concat([nm]);
    pos[nm] = { x: Math.max(30, Math.min(SIZE - 30, x)), y: Math.max(30, Math.min(SIZE - 30, y)) };
    selected = nm;
    commit(names, model.edges.slice(), {});
  }
  function deleteSelected() {
    var si = selected === null ? -1 : model.names.indexOf(selected);
    if (si < 0) return;
    var names = model.names.filter(function (_, i) { return i !== si; });
    var edges = [];
    model.edges.forEach(function (e) {
      if (e[0] === si || e[1] === si) return;
      edges.push([e[0] > si ? e[0] - 1 : e[0], e[1] > si ? e[1] - 1 : e[1]]);
    });
    delete pos[selected];
    selected = null;
    commit(names, edges, {});
  }
  function tap(i) {
    var nm = model.names[i];
    if (editMode && selected !== null && selected !== nm) { var a = selected; selected = null; toggleEdge(a, nm); return; }
    selected = selected === nm ? null : nm;
    renderAll();
  }

  svg.addEventListener('pointerdown', function (e) {
    var g = e.target.closest('g[data-i]');
    if (!g) {
      if (editMode) { var p = svgPoint(e); addVertex(p.x, p.y); }
      else if (selected !== null) { selected = null; renderAll(); }
      return;
    }
    drag = { i: +g.getAttribute('data-i'), sx: e.clientX, sy: e.clientY, moved: false };
    svg.setPointerCapture(e.pointerId);
  });
  svg.addEventListener('pointermove', function (e) {
    if (!drag) return;
    if (!drag.moved && Math.hypot(e.clientX - drag.sx, e.clientY - drag.sy) < 5) return;
    drag.moved = true;
    var p = svgPoint(e), r = nodeRadius(model.names.length) + 4;
    pos[model.names[drag.i]] = { x: Math.max(r, Math.min(SIZE - r, p.x)), y: Math.max(r, Math.min(SIZE - r, p.y)) };
    renderGraph();
  });
  svg.addEventListener('pointerup', function () {
    if (!drag) return;
    var i = drag.i, moved = drag.moved;
    drag = null;
    if (!moved) tap(i);
  });
  svg.addEventListener('keydown', function (e) {
    if (e.key !== 'Enter' && e.key !== ' ') return;
    var g = e.target.closest('g[data-i]');
    if (g) { e.preventDefault(); tap(+g.getAttribute('data-i')); }
  });
  document.addEventListener('keydown', function (e) {
    if ((e.key === 'Delete' || e.key === 'Backspace') && selected !== null && !/^(TEXTAREA|INPUT|SELECT)$/.test(document.activeElement.tagName)) {
      e.preventDefault(); deleteSelected();
    }
  });

  /* ---------- controls ---------- */
  var sel = $('preset');
  Object.keys(PRESETS).forEach(function (k) {
    var o = document.createElement('option'); o.value = k; o.textContent = PRESETS[k].label; sel.appendChild(o);
  });
  var custom = document.createElement('option'); custom.value = 'custom'; custom.textContent = 'Your own problem'; sel.appendChild(custom);

  function loadPreset(key) {
    var p = PRESETS[key];
    selected = null;
    $('noun').value = p.noun;
    src.value = p.text;
    $('copybox').hidden = true; $('note').textContent = '';
    applyText(p.text, { layout: p.layout });
  }
  sel.addEventListener('change', function () { if (sel.value !== 'custom') loadPreset(sel.value); });

  $('rand').addEventListener('click', function () {
    var n = 12, names = [], edges = [], i, j;
    for (i = 0; i < n; i++) names.push('V' + (i + 1));
    for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) if (Math.random() < 0.28) edges.push([i, j]);
    sel.value = 'custom'; selected = null; $('noun').value = 'Color';
    src.value = serialize(names, edges);
    applyText(src.value, { layout: 'force', animate: true });
  });

  src.addEventListener('input', function () {
    sel.value = 'custom';
    clearTimeout(typing);
    typing = setTimeout(function () { applyText(src.value, {}); }, 350);
  });
  $('noun').addEventListener('input', function () { renderAnswer(); renderGraph(); renderHint(); renderSel(); });

  $('edit').addEventListener('click', function () {
    editMode = !editMode;
    this.setAttribute('aria-pressed', editMode);
    selected = null;
    renderAll();
  });
  $('del').addEventListener('click', deleteSelected);
  $('tidy').addEventListener('click', function () { layoutAll('force'); renderGraph(); });
  $('replay').addEventListener('click', function () { if (result) { reduceMotion ? renderAll() : startReveal(); } });

  function resultText() {
    var word = noun(), out = [result.k + ' ' + plural(word, result.k) + (result.proven ? ' (minimum)' : ' (best found)')];
    for (var c = 0; c < result.k; c++) {
      var m = [];
      model.names.forEach(function (nm, i) { if (result.colors[i] === c) m.push(nm); });
      out.push(word + ' ' + (c + 1) + ': ' + m.join(', '));
    }
    return out.join('\n');
  }
  $('copy').addEventListener('click', function () {
    if (!result) return;
    var t = resultText(), box = $('copybox');
    function fallback() { box.hidden = false; box.value = t; box.select(); $('note').textContent = 'Press Ctrl+C or Cmd+C to copy.'; }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(t).then(function () { box.hidden = true; $('note').textContent = 'Copied.'; }, fallback);
    } else fallback();
  });

  loadPreset('fish');
})();