/*
 * solver.js  -  graph coloring algorithm (no DOM, works in the browser and in Node)
 *
 * solve(n, edges, opts)
 *   n      number of vertices, numbered 0 .. n-1
 *   edges  array of [a, b] pairs, a !== b (two vertices that must get different colors)
 *   opts   { timeLimitMs: 1500 }
 *
 * Returns { k, colors, proven, lowerBound, clique, proof, nodes, ms, edgeCount, maxDegree }
 *   k           number of colors used by the best coloring found
 *   colors[v]   color index (0 .. k-1) of vertex v
 *   proven      true when k is certainly the minimum (the chromatic number)
 *   lowerBound  smallest number of colors that can possibly work
 *   clique      a largest group of vertices that all conflict with each other
 *   proof       'clique' | 'search' | 'none'  (why k is minimal)
 *
 * Method:
 *   1. DSATUR greedy coloring gives a quick upper bound.
 *   2. A maximum clique gives a lower bound (a clique of size c needs c colors).
 *   3. If the bounds differ, a DSATUR branch-and-bound search tries to prove that
 *      fewer colors are impossible, or finds a better coloring.
 */
(function (root) {
  'use strict';

  function now() {
    return (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
  }

  function solve(n, edges, opts) {
    opts = opts || {};
    var limit = opts.timeLimitMs || 1500;
    var t0 = now();
    if (n === 0) return null;

    var i, adj = [], M = [];
    for (i = 0; i < n; i++) { adj.push([]); M.push(new Uint8Array(n)); }
    edges.forEach(function (e) {
      adj[e[0]].push(e[1]); adj[e[1]].push(e[0]);
      M[e[0]][e[1]] = 1; M[e[1]][e[0]] = 1;
    });
    var deg = adj.map(function (a) { return a.length; });
    var maxDegree = Math.max.apply(null, deg);

    /* 1. DSATUR greedy coloring (upper bound) */
    function dsatur() {
      var col = [], step, u, q, v, bs, bd, s, c, seen, used;
      for (i = 0; i < n; i++) col.push(-1);
      for (step = 0; step < n; step++) {
        v = -1; bs = -1; bd = -1;
        for (u = 0; u < n; u++) {
          if (col[u] >= 0) continue;
          seen = {}; s = 0;
          for (q = 0; q < adj[u].length; q++) {
            c = col[adj[u][q]];
            if (c >= 0 && !seen[c]) { seen[c] = 1; s++; }
          }
          if (s > bs || (s === bs && deg[u] > bd)) { v = u; bs = s; bd = deg[u]; }
        }
        used = {};
        for (q = 0; q < adj[v].length; q++) if (col[adj[v][q]] >= 0) used[col[adj[v][q]]] = 1;
        c = 0; while (used[c]) c++;
        col[v] = c;
      }
      return col;
    }
    var greedy = dsatur();
    var best = Math.max.apply(null, greedy) + 1;
    var bestCol = greedy.slice();

    /* 2. maximum clique (lower bound), Carraghan-Pardalos with a time cap */
    var clique = [];
    var cliqueDeadline = t0 + limit * 0.25;
    var cliqueSteps = 0, cliqueStop = false;
    function expand(R, P) {
      if (cliqueStop) return;
      if ((++cliqueSteps & 1023) === 0 && now() > cliqueDeadline) { cliqueStop = true; return; }
      if (P.length === 0) { if (R.length > clique.length) clique = R.slice(); return; }
      for (var a = 0; a < P.length; a++) {
        if (R.length + P.length - a <= clique.length) return;
        var v = P[a], np = [];
        for (var b = a + 1; b < P.length; b++) if (M[v][P[b]]) np.push(P[b]);
        R.push(v); expand(R, np); R.pop();
        if (cliqueStop) return;
      }
    }
    var order = [];
    for (i = 0; i < n; i++) order.push(i);
    order.sort(function (a, b) { return deg[b] - deg[a] || a - b; });
    expand([], order);
    if (clique.length === 0) clique = [0];
    clique.sort(function (a, b) { return a - b; });

    /* 3. exact DSATUR branch and bound */
    var nodes = 0, timedOut = false, proof = 'clique';
    if (clique.length < best) {
      proof = 'search';
      var deadline = t0 + limit, target = clique.length;
      var col = [], cnt = [], sat = new Int32Array(n);
      for (i = 0; i < n; i++) { col.push(-1); cnt.push(new Int32Array(n + 1)); }
      var rec = function (colored, used) {
        if (timedOut || best === target) return;
        nodes++;
        if ((nodes & 1023) === 0 && now() > deadline) { timedOut = true; return; }
        if (colored === n) {
          if (used < best) { best = used; bestCol = col.slice(); }
          return;
        }
        var v = -1, bs = -1, bd = -1, u, a, w, c;
        for (u = 0; u < n; u++) {
          if (col[u] >= 0) continue;
          if (sat[u] > bs || (sat[u] === bs && deg[u] > bd)) { v = u; bs = sat[u]; bd = deg[u]; }
        }
        for (c = 0; c <= Math.min(used, best - 2); c++) {
          if (cnt[v][c]) continue;
          col[v] = c;
          for (a = 0; a < adj[v].length; a++) { w = adj[v][a]; if (cnt[w][c]++ === 0) sat[w]++; }
          rec(colored + 1, c === used ? used + 1 : used);
          for (a = 0; a < adj[v].length; a++) { w = adj[v][a]; if (--cnt[w][c] === 0) sat[w]--; }
          col[v] = -1;
          if (timedOut || best === target) return;
        }
      };
      rec(0, 0);
      if (best === clique.length) proof = 'clique';
      if (timedOut) proof = 'none';
    }

    return {
      k: best,
      colors: bestCol,
      proven: !timedOut,
      lowerBound: timedOut ? clique.length : best,
      clique: clique,
      proof: proof,
      nodes: nodes,
      ms: Math.round(now() - t0),
      edgeCount: edges.length,
      maxDegree: maxDegree
    };
  }

  var api = { solve: solve };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.GraphSolver = api;
})(typeof window !== 'undefined' ? window : this);