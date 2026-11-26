/* ==========================================================================
   CADMO Interactive Proof Reader Controller
   Print-authentic monograph reader: calm whitespace, on-demand sidenotes,
   zero diagram clutter in the reading flow, real 2D offline math.
   ========================================================================== */
(() => {
  let doc = {};

  const state = {
    mode: "paper",
    expanded: new Set(),
    inspector: null,        // null | { type: "symbol", item } | { type: "goal", goal, label } | { type: "axioms", entry }
    glossaryOpen: false,    // hidden by default so right margin is pure calm paper
    glossaryQuery: "",
    theme: "light"          // archival paper by default
  };

  const secNumById = new Map();
  const sectionContextById = new Map();
  const sectionRefKeys = new Map();
  const inspectorByKey = new Map();

  function stripEmbeddedStyles(htmlStr) {
    if (!htmlStr) return "";
    return String(htmlStr).replace(/<style\b[^>]*>[\s\S]*?<\/style>/gi, "");
  }

  function sanitizeProofNodes(nodes) {
    if (!Array.isArray(nodes)) return;
    for (const node of nodes) {
      if (!node || typeof node !== "object") continue;
      if (typeof node.diagramHtml === "string") {
        node.diagramHtml = stripEmbeddedStyles(node.diagramHtml);
      }
      if (node.kind === "figure" && typeof node.html === "string") {
        node.html = stripEmbeddedStyles(node.html);
      }
      if (Array.isArray(node.children)) sanitizeProofNodes(node.children);
      if (Array.isArray(node.details)) sanitizeProofNodes(node.details);
      if (Array.isArray(node.steps)) {
        for (const item of node.steps) {
          if (!item || typeof item !== "object") continue;
          if (item.step && typeof item.step.diagramHtml === "string") {
            item.step.diagramHtml = stripEmbeddedStyles(item.step.diagramHtml);
          }
          if (Array.isArray(item.children)) sanitizeProofNodes(item.children);
        }
      }
    }
  }

  function sanitizeDocDiagrams(targetDoc) {
    if (!targetDoc || typeof targetDoc !== "object") return;
    const sanitizeIns = (ins) => {
      if (ins && ins.kind && ins.kind.ccDiagram && typeof ins.kind.ccDiagram.svgOrHtml === "string") {
        ins.kind.ccDiagram.svgOrHtml = stripEmbeddedStyles(ins.kind.ccDiagram.svgOrHtml);
      }
    };
    for (const ins of targetDoc.inspectors || []) sanitizeIns(ins);
    for (const entry of targetDoc.entries || []) {
      if (!entry || typeof entry !== "object") continue;
      if (typeof entry.diagramHtml === "string") {
        entry.diagramHtml = stripEmbeddedStyles(entry.diagramHtml);
      }
      if (Array.isArray(entry.sectionPreludes)) {
        for (const p of entry.sectionPreludes) {
          if (p && typeof p === "object" && typeof p.diagramHtml === "string") {
            p.diagramHtml = stripEmbeddedStyles(p.diagramHtml);
          }
        }
      }
      for (const ins of entry.localInspectors || []) sanitizeIns(ins);
      if (entry.sectionContext && Array.isArray(entry.sectionContext.inspectors)) {
        for (const ins of entry.sectionContext.inspectors) sanitizeIns(ins);
      }
      sanitizeProofNodes(entry.proof);
    }
  }

  function initDocumentIndexes(targetDoc) {
    secNumById.clear();
    sectionContextById.clear();
    sectionRefKeys.clear();
    inspectorByKey.clear();
    for (const ins of targetDoc.inspectors || []) {
      inspectorByKey.set(ins.key, ins);
    }
    let sNum = 0;
    let curSecId = null;
    for (const entry of targetDoc.entries || []) {
      if (entry.sectionTitle) {
        sNum += 1;
        curSecId = (entry.sectionContext && entry.sectionContext.sectionId) ||
          entry.sectionId || `sec-${sNum}`;
        const realNum = (entry.sectionContext && entry.sectionContext.sectionNumber) || sNum;
        secNumById.set(curSecId, realNum);
        if (entry.sectionContext) {
          sectionContextById.set(curSecId, entry.sectionContext);
          for (const ins of entry.sectionContext.inspectors || []) {
            inspectorByKey.set(ins.key, ins);
          }
        }
      }
      const eSecId = (entry.sectionContext && entry.sectionContext.sectionId) ||
        entry.sectionId || curSecId;
      if (eSecId && Array.isArray(entry.referencedKeys)) {
        if (!sectionRefKeys.has(eSecId)) sectionRefKeys.set(eSecId, new Set());
        const sset = sectionRefKeys.get(eSecId);
        for (const k of entry.referencedKeys) sset.add(k);
      }
      if (eSecId && Array.isArray(entry.sectionPreludes)) {
        if (!sectionRefKeys.has(eSecId)) sectionRefKeys.set(eSecId, new Set());
        const sset = sectionRefKeys.get(eSecId);
        for (const p of entry.sectionPreludes) {
          if (p && p.declKey) sset.add(p.declKey);
        }
      }
      for (const ins of entry.localInspectors || []) {
        inspectorByKey.set(ins.key, ins);
      }
    }
  }

  function isGlossaryWorthy(ins) {
    if (!ins || !ins.kind) return false;
    if (ins.kind.parameter || ins.kind.localShorthand) return false;
    const key = ins.key || "";
    if (
      key.startsWith("sec:") ||
      key.startsWith("secparam:") ||
      key.startsWith("param:") ||
      key.startsWith("shorthand:") ||
      key.startsWith("inst") ||
      key.startsWith("CategoryTheory.") ||
      key.includes(".inst") ||
      key.endsWith(".toCategoryStruct") ||
      key.endsWith(".absorb") ||
      key.endsWith(".ClosedUnder") ||
      key === "SystemAlgebra.TypedSystem" ||
      key === "SystemAlgebra.TypedConverter" ||
      key === "SystemAlgebra.TypedDistinguisher"
    ) {
      return false;
    }
    return true;
  }

  function glossaryCategory(ins) {
    const k = ins.kind || {};
    if (ins.roleBadge === "theorem") return "Cited Results";
    if (k.interfaceTable) return "Interfaces";
    if (k.dslPseudocode || k.ccDiagram) return "Systems & Converters";
    if (k.witnessCard) return "Proof Witnesses";
    return "Definitions";
  }

  /* ------------------------------------------------------------------------
     Real 2D offline HTML math renderer (no external CDN required; upgrades
     automatically to KaTeX if loaded).
     ------------------------------------------------------------------------ */
  function skipMathSpaces(str, pos) {
    while (pos < str.length && /\s/.test(str[pos])) pos++;
    return pos;
  }

  function readOptionalBracket(str, pos) {
    const p = skipMathSpaces(str, pos);
    if (p >= str.length || str[p] !== "[") return [null, pos];
    let depth = 1;
    let braceDepth = 0;
    let j = p + 1;
    while (j < str.length && depth > 0) {
      if (str[j] === "{") braceDepth++;
      else if (str[j] === "}" && braceDepth > 0) braceDepth--;
      else if (braceDepth === 0) {
        if (str[j] === "[") depth++;
        else if (str[j] === "]") depth--;
      }
      j++;
    }
    return [str.slice(p + 1, Math.max(p + 1, j - 1)), j];
  }

  function readBalanced(str, pos) {
    pos = skipMathSpaces(str, pos);
    if (pos >= str.length) return ["", pos];
    if (str[pos] === "{") {
      let depth = 1;
      let j = pos + 1;
      while (j < str.length && depth > 0) {
        if (str[j] === "{") depth++;
        else if (str[j] === "}") depth--;
        j++;
      }
      return [str.slice(pos + 1, Math.max(pos + 1, j - 1)), j];
    }
    if (str[pos] === "\\") {
      let j = pos + 1;
      while (j < str.length && /[A-Za-z]/.test(str[j])) j++;
      if (j === pos + 1 && j < str.length) j++;
      return [str.slice(pos, j), j];
    }
    return [str[pos], pos + 1];
  }

  const SYMBOL_MAP = {
    varepsilon: "ε", epsilon: "ε", Delta: "Δ", Gamma: "Γ", Pi: "Π", Sigma: "Σ",
    Phi: "Φ", Psi: "Ψ", Omega: "Ω", Lambda: "Λ", Theta: "Θ",
    alpha: "α", beta: "β", gamma: "γ", delta: "δ", zeta: "ζ", eta: "η",
    theta: "θ", iota: "ι", kappa: "κ", lambda: "λ", mu: "μ", nu: "ν",
    pi: "π", rho: "ρ", sigma: "σ", tau: "τ", phi: "φ", varphi: "φ",
    chi: "χ", psi: "ψ", omega: "ω", ell: "ℓ", star: "★", bullet: "•",
    varnothing: "∅", emptyset: "∅", infty: "∞",
    parallel: "∥", otimes: "⊗", oplus: "⊕", equiv: "≡", simeq: "≃", approx: "≈",
    cong: "≅", sim: "∼", models: "⊨", vdash: "⊢", Vdash: "⊩",
    le: "≤", ge: "≥", ne: "≠", neq: "≠", implies: "⇒", iff: "⇔",
    in: "∈", notin: "∉", subseteq: "⊆", times: "×", cdot: "·", circ: "∘",
    to: "→", rightarrow: "→", leftarrow: "←", gets: "←", leftrightarrow: "↔",
    Leftarrow: "⇐", Rightarrow: "⇒", Leftrightarrow: "⇔",
    mapsto: "↦", forall: "∀", exists: "∃", land: "∧", wedge: "∧",
    lor: "∨", vee: "∨", neg: "¬", sum: "∑", prod: "∏", pm: "±",
    mid: "∣", preceq: "⪯", succeq: "⪰", top: "⊤", bot: "⊥", perp: "⊥",
    triangleright: "▷", triangleleft: "◁", bigsqcup: "⊔", sqcup: "⊔",
    ldots: "…", cdots: "⋯", dots: "…", colon: ":", setminus: "∖",
    cup: "∪", cap: "∩", subset: "⊂", supseteq: "⊇",
    langle: "⟨", rangle: "⟩", lfloor: "⌊", rfloor: "⌋", lceil: "⌈", rceil: "⌉",
    Vert: "∥", vert: "|",
    quad: "\u2003", qquad: "\u2003\u2003", thinspace: "\u2009", enspace: "\u2002",
    prime: "′",
    Pr: "Pr", min: "min", max: "max", log: "log", exp: "exp"
  };

  function renderMathNodes(tex) {
    const frag = document.createDocumentFragment();
    let i = 0;
    while (i < tex.length) {
      const ch = tex[i];
      if (ch === "{") {
        const [inner, next] = readBalanced(tex, i);
        frag.appendChild(renderMathNodes(inner));
        i = next;
        continue;
      }
      if (ch === "^" || ch === "_") {
        const tag = ch === "^" ? "sup" : "sub";
        const [arg, next] = readBalanced(tex, i + 1);
        const el = document.createElement(tag);
        el.appendChild(renderMathNodes(arg));
        frag.appendChild(el);
        i = next;
        continue;
      }
      if (ch === "\\") {
        let j = i + 1;
        while (j < tex.length && /[A-Za-z]/.test(tex[j])) j++;
        if (j === i + 1) {
          const esc = tex[i + 1] || "";
          if (esc === "," || esc === ";") frag.appendChild(document.createTextNode("\u2009"));
          else if (esc === "!") { /* thin negative space */ }
          else if (esc === "|") frag.appendChild(document.createTextNode("∥"));
          else frag.appendChild(document.createTextNode(esc));
          i += 2;
          continue;
        }
        const cmd = tex.slice(i + 1, j);
        i = j;
        if (cmd === "left" || cmd === "right") continue;
        if (cmd === "begin") {
          const [envName, afterBegin] = readBalanced(tex, i);
          const endTag = `\\end{${envName}}`;
          const endIdx = tex.indexOf(endTag, afterBegin);
          if (envName === "cases" && endIdx !== -1) {
            const inner = tex.slice(afterBegin, endIdx);
            const rows = inner.split(/\\\\/);
            const wrap = document.createElement("span");
            wrap.className = "cadmo-cases";
            const brace = document.createElement("span");
            brace.className = "cadmo-cases-brace";
            brace.textContent = "{";
            wrap.appendChild(brace);
            const body = document.createElement("span");
            body.className = "cadmo-cases-body";
            for (const rawRow of rows) {
              const trimmed = rawRow.trim();
              if (!trimmed) continue;
              const rowEl = document.createElement("span");
              rowEl.className = "cadmo-cases-row";
              const cols = trimmed.split("&");
              cols.forEach((col, ci) => {
                const cell = document.createElement("span");
                cell.className = ci === 0 ? "cadmo-cases-val" : "cadmo-cases-cond";
                cell.appendChild(renderMathNodes(col.trim()));
                rowEl.appendChild(cell);
              });
              body.appendChild(rowEl);
            }
            wrap.appendChild(body);
            frag.appendChild(wrap);
            i = endIdx + endTag.length;
            continue;
          }
          i = afterBegin;
          continue;
        }
        if (cmd === "end") {
          const [, afterEnd] = readBalanced(tex, i);
          i = afterEnd;
          continue;
        }
        if (cmd === "frac") {
          const [num, p1] = readBalanced(tex, i);
          const [den, p2] = readBalanced(tex, p1);
          const wrap = document.createElement("span");
          wrap.className = "cadmo-frac";
          const nEl = document.createElement("span");
          nEl.className = "cadmo-num";
          nEl.appendChild(renderMathNodes(num));
          const dEl = document.createElement("span");
          dEl.className = "cadmo-den";
          dEl.appendChild(renderMathNodes(den));
          wrap.appendChild(nEl);
          wrap.appendChild(dEl);
          frag.appendChild(wrap);
          i = p2;
          continue;
        }
        if (cmd === "binom") {
          const [n, p1] = readBalanced(tex, i);
          const [k, p2] = readBalanced(tex, p1);
          frag.appendChild(document.createTextNode("C("));
          frag.appendChild(renderMathNodes(n));
          frag.appendChild(document.createTextNode(", "));
          frag.appendChild(renderMathNodes(k));
          frag.appendChild(document.createTextNode(")"));
          i = p2;
          continue;
        }
        if (cmd === "xleftarrow" || cmd === "xrightarrow") {
          const [below, p1] = readOptionalBracket(tex, i);
          const [above, p2] = readBalanced(tex, p1);
          const wrap = document.createElement("span");
          wrap.className = "cadmo-xarrow cadmo-math-over";
          if (above && above.trim()) {
            const topEl = document.createElement("span");
            topEl.className = "cadmo-xarrow-top";
            topEl.appendChild(renderMathNodes(above.trim()));
            wrap.appendChild(topEl);
          }
          const midEl = document.createElement("span");
          midEl.className = "cadmo-xarrow-mid cadmo-msym";
          midEl.textContent = cmd === "xleftarrow" ? "←" : "→";
          wrap.appendChild(midEl);
          if (below && below.trim()) {
            wrap.classList.add("has-below");
            const botEl = document.createElement("span");
            botEl.className = "cadmo-xarrow-bot";
            botEl.appendChild(renderMathNodes(below.trim()));
            wrap.appendChild(botEl);
          }
          frag.appendChild(wrap);
          i = p2;
          continue;
        }
        if (cmd === "mathbb") {
          const [arg, next] = readBalanced(tex, i);
          const bb = { R: "ℝ", N: "ℕ", Z: "ℤ", Q: "ℚ", C: "ℂ" }[arg] || arg;
          const span = document.createElement("span");
          span.className = "cadmo-msym cadmo-bb";
          span.textContent = bb;
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (cmd === "mathcal") {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          span.className = "cadmo-cal";
          if (arg.includes("\\")) span.appendChild(renderMathNodes(arg));
          else span.textContent = arg;
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (
          cmd === "hat" || cmd === "widehat" || cmd === "tilde" || cmd === "widetilde" ||
          cmd === "bar" || cmd === "overline" || cmd === "vec"
        ) {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          const kindCls = (cmd === "hat" || cmd === "widehat") ? "hat"
            : (cmd === "tilde" || cmd === "widetilde") ? "tilde"
            : (cmd === "bar" || cmd === "overline") ? "bar"
            : "vec";
          const trimmed = arg.trim();
          const bareChars = trimmed
            .replace(/\\(?:mathbf|boldsymbol|mathcal|mathsf|mathbb|mathrm|mathit|operatorname|text)\{([^{}]*)\}/g, "$1")
            .replace(/\\[A-Za-z]+/g, "x")
            .replace(/[{}\s^_]/g, "");
          const isWide = cmd === "widehat" || cmd === "widetilde" || cmd === "overline" || bareChars.length > 1;
          const isShort = bareChars.length === 1 && /^[acemnor-su-z]$/.test(bareChars) && !/\\(?:mathbf|mathcal|mathbb|mathsf)/.test(trimmed);
          span.className = `cadmo-accent cadmo-accent-${kindCls}` +
            (isWide ? " cadmo-accent-wide" : "") +
            (isShort ? " cadmo-accent-short" : "");
          span.setAttribute("data-accent", cmd);
          const base = document.createElement("span");
          base.className = "cadmo-accent-base";
          base.appendChild(renderMathNodes(arg));
          span.appendChild(base);
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (cmd === "underline") {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          span.className = "cadmo-math-underline";
          span.appendChild(renderMathNodes(arg));
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (
          cmd === "mathrm" || cmd === "mathsf" || cmd === "operatorname" ||
          cmd === "text" || cmd === "texttt" || cmd === "mathtt" ||
          cmd === "mathbf" || cmd === "boldsymbol" || cmd === "mathrel" ||
          cmd === "mathbin" || cmd === "mathord" || cmd === "mathit"
        ) {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          if (cmd === "text" || cmd === "texttt" || cmd === "mathtt") {
            span.className = (cmd === "texttt" || cmd === "mathtt") ? "cadmo-mtext cadmo-tt" : "cadmo-mtext";
            if (cmd === "texttt" || cmd === "mathtt") span.style.fontFamily = "var(--font-mono)";
            span.textContent = arg.replace(/\\_/g, "_");
          } else if (cmd === "mathbin") {
            span.className = "cadmo-msym";
            span.appendChild(document.createTextNode(" "));
            span.appendChild(renderMathNodes(arg));
            span.appendChild(document.createTextNode(" "));
          } else if (cmd === "mathbf" || cmd === "boldsymbol") {
            span.className = "cadmo-op cadmo-bf";
            span.style.fontWeight = "600";
            span.appendChild(renderMathNodes(arg));
          } else if (cmd === "mathsf") {
            span.className = "cadmo-op cadmo-sf";
            if (/\\(?![_])/.test(arg)) span.appendChild(renderMathNodes(arg));
            else span.textContent = arg.replace(/\\_/g, "_");
          } else {
            span.className = "cadmo-op";
            if (cmd === "mathrel") span.classList.add("cadmo-mrel-op");
            if (cmd === "mathrm" || cmd === "operatorname" || cmd === "mathit") {
              if (/\\(?![_])/.test(arg)) span.appendChild(renderMathNodes(arg));
              else span.textContent = arg.replace(/\\_/g, "_");
            } else {
              span.appendChild(renderMathNodes(arg));
            }
          }
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (SYMBOL_MAP[cmd] !== undefined) {
          const span = document.createElement("span");
          span.className = (cmd === "triangleright" || cmd === "triangleleft")
            ? "cadmo-msym cadmo-msym-tri"
            : "cadmo-msym";
          span.textContent = SYMBOL_MAP[cmd];
          frag.appendChild(span);
          continue;
        }
        const unknownSpan = document.createElement("span");
        unknownSpan.className = "cadmo-msym";
        unknownSpan.textContent = cmd;
        frag.appendChild(unknownSpan);
        continue;
      }
      if (/[A-Za-z]/.test(ch)) {
        const v = document.createElement("var");
        v.textContent = ch;
        frag.appendChild(v);
        i++;
        continue;
      }
      if (ch === "'") {
        let k = i;
        while (k < tex.length && tex[k] === "'") k++;
        let rem = k - i;
        let primes = "";
        while (rem >= 3) {
          primes += "\u2034";
          rem -= 3;
        }
        if (rem === 2) primes += "\u2033";
        else if (rem === 1) primes += "\u2032";
        const span = document.createElement("span");
        span.className = "cadmo-msym cadmo-prime";
        span.textContent = primes;
        frag.appendChild(span);
        i = k;
        continue;
      }
      frag.appendChild(document.createTextNode(ch));
      i++;
    }
    return frag;
  }

  /* ------------------------------------------------------------------------
     Automatic CBC / VS Code–style Reference Normalization & Math Annotator
     ------------------------------------------------------------------------ */
  const UNICODE_SCRIPT_MAP = {
    "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4",
    "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9",
    "⁺": "+", "⁻": "-", "⁰": "0", "¹": "1", "²": "2",
    "³": "3", "⁴": "4", "⁵": "5", "⁶": "6", "⁷": "7",
    "⁸": "8", "⁹": "9"
  };

  const FONT_PREFIX_RE = /^(cal|bf|sf|bb):/;
  const BLOCKED_HOVER_SELECTOR =
    "sup, sub, .msupsub, .op-limits, .accent-body, .mopen, .mclose, .mpunct, .mbin, .mrel, .cadmo-mtext, .mtext";

  function stripFontPrefix(norm) {
    return String(norm || "").replace(FONT_PREFIX_RE, "");
  }

  function extractFontPrefixFromLatex(raw) {
    if (!raw) return "";
    let s = String(raw).trim();
    let prev;
    do {
      prev = s;
      s = s
        .replace(/^\{+/, "")
        .replace(/^\\(?:widehat|widetilde|overline|underline|hat|tilde|bar|vec)\s*(?:\{\s*)?/, "")
        .trim();
    } while (s !== prev);
    const m = s.match(/^\\(mathcal|mathbf|boldsymbol|mathsf|mathbb)(?:\s*\{|\s+|\b)/);
    if (m) {
      switch (m[1]) {
        case "mathcal": return "cal:";
        case "mathbf":
        case "boldsymbol": return "bf:";
        case "mathsf": return "sf:";
        case "mathbb": return "bb:";
      }
    }
    const firstCp = s.codePointAt(0);
    if (firstCp !== undefined) {
      if (firstCp >= 0x1d400 && firstCp <= 0x1d433) return "bf:";
      if ((firstCp >= 0x1d49c && firstCp <= 0x1d503) ||
          "ℬℰℱℋℐℒℳℛ".includes(String.fromCodePoint(firstCp))) return "cal:";
      if (firstCp >= 0x1d5a0 && firstCp <= 0x1d607) return "sf:";
      if ((firstCp >= 0x1d538 && firstCp <= 0x1d56b) ||
          "ℝℕℤℚℂ".includes(String.fromCodePoint(firstCp))) return "bb:";
    }
    return "";
  }

  function normalizeUnicodeMath(str) {
    const primeMap = {
      "\u2032": "'", "\u2033": "''", "\u2034": "'''", "\u2057": "''''"
    };
    const scriptMap = {
      "ℬ": "B", "ℰ": "E", "ℱ": "F", "ℋ": "H", "ℐ": "I", "ℒ": "L", "ℳ": "M", "ℛ": "R",
      "ℯ": "e", "ℊ": "g", "ℴ": "o",
      "ℝ": "R", "ℕ": "N", "ℤ": "Z", "ℚ": "Q", "ℂ": "C", "ℍ": "H", "ℙ": "P"
    };
    return Array.from(str || "").map((ch) => {
      if (primeMap[ch] !== undefined) return primeMap[ch];
      if (UNICODE_SCRIPT_MAP[ch] !== undefined) return UNICODE_SCRIPT_MAP[ch];
      if (scriptMap[ch] !== undefined) return scriptMap[ch];
      const cp = ch.codePointAt(0);
      if (cp >= 0x1d400 && cp <= 0x1d419) return String.fromCharCode(65 + (cp - 0x1d400));
      if (cp >= 0x1d41a && cp <= 0x1d433) return String.fromCharCode(97 + (cp - 0x1d41a));
      if (cp >= 0x1d434 && cp <= 0x1d44d) return String.fromCharCode(65 + (cp - 0x1d434));
      if (cp >= 0x1d44e && cp <= 0x1d467) return String.fromCharCode(97 + (cp - 0x1d44e));
      if (cp >= 0x1d49c && cp <= 0x1d4b5) return String.fromCharCode(65 + (cp - 0x1d49c));
      if (cp >= 0x1d4b6 && cp <= 0x1d4cf) return String.fromCharCode(97 + (cp - 0x1d4b6));
      if (cp >= 0x1d4d0 && cp <= 0x1d4e9) return String.fromCharCode(65 + (cp - 0x1d4d0));
      if (cp >= 0x1d4ea && cp <= 0x1d503) return String.fromCharCode(97 + (cp - 0x1d4ea));
      if (cp >= 0x1d5a0 && cp <= 0x1d5b9) return String.fromCharCode(65 + (cp - 0x1d5a0));
      if (cp >= 0x1d5ba && cp <= 0x1d5d3) return String.fromCharCode(97 + (cp - 0x1d5ba));
      if (cp >= 0x1d5d4 && cp <= 0x1d5ed) return String.fromCharCode(65 + (cp - 0x1d5d4));
      if (cp >= 0x1d5ee && cp <= 0x1d607) return String.fromCharCode(97 + (cp - 0x1d5ee));
      return ch;
    }).join("");
  }

  function normalizeMathToken(raw, fontPrefixOverride = null) {
    if (!raw) return "";
    const prefix = fontPrefixOverride || extractFontPrefixFromLatex(raw);
    let s = normalizeUnicodeMath(String(raw)).replace(/[\u200b\u2009]/g, "");
    let prev;
    do {
      prev = s;
      s = s
        .replace(/\\(?:mathrm|mathit|mathsf|mathbf|mathcal|mathbb|operatorname|text|texttt|boldsymbol|widehat|widetilde|overline|underline|hat|tilde|bar|vec)\{([^{}]*)\}/g, "$1");
    } while (s !== prev);
    s = s
      .replace(/\\(?:mathrm|mathit|mathsf|mathbf|mathcal|mathbb|operatorname|text|texttt|boldsymbol|widehat|widetilde|overline|underline|hat|tilde|bar|vec)\b\s*/g, "")
      .replace(/\\(?:left|right|middle)\b/g, "")
      .replace(/\\[!,;: ]/g, "")
      .replace(/\\_/g, "_")
      .replace(/\\([A-Za-z]+)/g, (_, cmd) => (SYMBOL_MAP[cmd] !== undefined ? SYMBOL_MAP[cmd] : cmd))
      .replace(/\u2032/g, "'")
      .replace(/\u2033/g, "''")
      .replace(/\u2034/g, "'''")
      .replace(/\u2057/g, "''''")
      .replace(/[\u0300-\u036f\u20d0-\u20ff]/g, "")
      .replace(/[{}_^\s]/g, "");
    if (!s) return "";
    return prefix + s;
  }

  const NON_TOKEN_RE = /^[0-9()[\]{},.;:=<>+\-*/·⋅∣|!?~'"\\⟨⟩≤≥≠≡≃≈⇒⇔∈∉⊆×∘→←↔⇐↦∀∃∧∨¬∑∏±⪯⪰⊤⊥▷◁•⊔∖∼≅⊨⊢⊩…\s]+$/;
  const elementCandidates = new WeakMap();
  const hoverInteractiveNodes = new Set();

  function isNonHoverableToken(norm) {
    if (!norm) return true;
    const bare = stripFontPrefix(norm);
    if (!bare || bare.length > 48) return true;
    return NON_TOKEN_RE.test(bare);
  }

  function buildTokenScope(localInspectors, sectionInspectors, docInspectors, sectionId, referencedKeys, includeSectionContextDefs = false) {
    const tokenMap = new Map();
    const tierMap = new Map(); // norm -> tier (1=local, 2=section, 3=global)

    function addCandidate(ins, tier) {
      if (!ins || !ins.display) return;
      const norm = normalizeMathToken(ins.display);
      if (isNonHoverableToken(norm)) return;
      const existingTier = tierMap.get(norm);
      if (existingTier !== undefined && existingTier < tier) return; // local shadows section/global
      if (existingTier === undefined || tier < existingTier) {
        tierMap.set(norm, tier);
        tokenMap.set(norm, [ins]);
        return;
      }
      const list = tokenMap.get(norm) || [];
      if (!list.some((x) => x.key === ins.key)) {
        list.push(ins);
        tokenMap.set(norm, list);
      }
    }

    for (const ins of localInspectors || []) addCandidate(ins, 1);
    for (const ins of sectionInspectors || []) addCandidate(ins, 2);

    const refSet = new Set(referencedKeys || []);
    const useRefFilter = refSet.size > 0 && !includeSectionContextDefs;
    for (const ins of docInspectors || []) {
      if (ins.sectionId && sectionId && ins.sectionId !== sectionId) continue;
      const k = ins.key || "";
      if (k.startsWith("sec:") || k.startsWith("param:") || k.startsWith("shorthand:") || k.startsWith("secparam:")) continue;
      if (useRefFilter && !refSet.has(k)) continue;
      addCandidate(ins, 3);
    }
    // Fallback: if Section Context mentions definitions/predicates not explicitly in sectionRefKeys
    if (includeSectionContextDefs || refSet.size === 0) {
      for (const ins of docInspectors || []) {
        if (ins.sectionId && sectionId && ins.sectionId !== sectionId) continue;
        const k = ins.key || "";
        if (k.startsWith("sec:") || k.startsWith("param:") || k.startsWith("shorthand:") || k.startsWith("secparam:")) continue;
        addCandidate(ins, 3);
      }
    }

    return { tokenMap, uniqueBareMap: buildUniqueBareMap(tokenMap), sectionId: sectionId || null };
  }

  function buildUniqueBareMap(tokenMap) {
    const bareMap = new Map();
    for (const [normKey, cands] of tokenMap.entries()) {
      const bare = stripFontPrefix(normKey);
      if (!bare) continue;
      if (!bareMap.has(bare)) bareMap.set(bare, []);
      const list = bareMap.get(bare);
      for (const ins of cands) {
        if (!list.some((x) => x.key === ins.key)) list.push(ins);
      }
    }
    const uniqueBareMap = new Map();
    for (const [bare, list] of bareMap.entries()) {
      if (list.length === 1) uniqueBareMap.set(bare, list);
    }
    return uniqueBareMap;
  }

  function resolveTokenCandidates(scope, norm) {
    if (!scope || !norm || isNonHoverableToken(norm)) return null;
    const exact = scope.tokenMap && scope.tokenMap.get(norm);
    if (exact && exact.length > 0) return exact;
    if (scope.uniqueBareMap) {
      const bare = stripFontPrefix(norm);
      const fallback = scope.uniqueBareMap.get(bare);
      if (fallback && fallback.length > 0) return fallback;
    }
    return null;
  }

  function buildScope(localInspectors, sectionId, referencedKeys, includeSectionContextDefs = false) {
    const secCtx = sectionId ? sectionContextById.get(sectionId) : null;
    return buildTokenScope(
      localInspectors,
      secCtx ? (secCtx.inspectors || []) : [],
      doc.inspectors || [],
      sectionId,
      referencedKeys,
      includeSectionContextDefs
    );
  }

  let activePopover = { anchor: null, candidates: [], index: 0 };
  let hidePopoverTimer = null;
  let popoverEl = null;
  let marginElRef = null;

  function syncActiveAriaPressed() {
    const activeKey = state.inspector && state.inspector.type === "symbol"
      ? state.inspector.item.key : null;
    for (const el of hoverInteractiveNodes) {
      if (!el.isConnected) {
        hoverInteractiveNodes.delete(el);
        continue;
      }
      const cands = elementCandidates.get(el) || [];
      const pressed = !!activeKey && cands.some((c) => c.key === activeKey);
      el.setAttribute("aria-pressed", pressed ? "true" : "false");
    }
  }

  function attachInteractiveToken(el, candidates, displayHint, tokenKey = null) {
    elementCandidates.set(el, candidates);
    hoverInteractiveNodes.add(el);
    if (tokenKey && el.dataset) el.dataset.cadmoToken = tokenKey;
    el.setAttribute("tabindex", "0");
    el.setAttribute("role", "button");
    const activeKey = state.inspector && state.inspector.type === "symbol"
      ? state.inspector.item.key : null;
    const isPressed = !!activeKey && candidates.some((c) => c.key === activeKey);
    el.setAttribute("aria-pressed", isPressed ? "true" : "false");
    if (displayHint && !el.getAttribute("aria-label")) {
      el.setAttribute("aria-label", `Inspect ${displayHint}`);
    }
    el.addEventListener("mouseenter", () => showPopover(el, candidates));
    el.addEventListener("focusin", () => showPopover(el, candidates));
    el.addEventListener("mouseleave", () => scheduleHidePopover(160));
    el.addEventListener("focusout", (ev) => {
      if (popoverEl && popoverEl.contains(ev.relatedTarget)) return;
      scheduleHidePopover(160);
    });
    el.addEventListener("click", (ev) => {
      ev.stopPropagation();
      const idx = activePopover.anchor === el ? activePopover.index : 0;
      const chosen = candidates[idx] || candidates[0];
      if (!chosen) return;
      state.inspector = { type: "symbol", item: chosen };
      hidePopover(true);
      renderMarginOnly();
    });
    el.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter" || ev.key === " ") {
        ev.preventDefault();
        el.click();
      } else if (ev.key === "Escape") {
        hidePopover(true);
      }
    });
  }

  function isSubAtomEl(node) {
    return node && node.nodeType === 1 &&
      (node.tagName === "VAR" ||
       node.classList.contains("cadmo-op") ||
       node.classList.contains("cadmo-cal") ||
       node.classList.contains("cadmo-msym"));
  }

  function isBlockedHoverNode(node) {
    if (!node || node.nodeType !== 1) return false;
    if (node.tagName === "SUP" || node.tagName === "SUB") return true;
    const cl = node.classList;
    if (!cl) return false;
    return (
      cl.contains("msupsub") ||
      cl.contains("op-limits") ||
      cl.contains("accent-body") ||
      cl.contains("mopen") ||
      cl.contains("mclose") ||
      cl.contains("mpunct") ||
      cl.contains("mbin") ||
      cl.contains("mrel") ||
      cl.contains("cadmo-mtext") ||
      cl.contains("mtext")
    );
  }

  function hasBlockedHoverAncestor(node) {
    if (!node || node.nodeType !== 1) return false;
    if (typeof node.closest === "function") {
      return !!node.closest(BLOCKED_HOVER_SELECTOR);
    }
    let cur = node.parentNode;
    while (cur && cur.nodeType === 1) {
      if (isBlockedHoverNode(cur)) return true;
      cur = cur.parentNode;
    }
    return false;
  }

  function fontPrefixOfSingleElement(el) {
    if (!el || el.nodeType !== 1) return "";
    const cl = el.classList;
    if (cl) {
      if (cl.contains("cadmo-cal") || cl.contains("mathcal")) return "cal:";
      if (cl.contains("cadmo-bf") || cl.contains("mathbf") || cl.contains("boldsymbol")) return "bf:";
      if (cl.contains("cadmo-sf") || cl.contains("mathsf")) return "sf:";
      if (cl.contains("cadmo-bb") || cl.contains("mathbb")) return "bb:";
    }
    if (el.style && (el.style.fontWeight === "bold" || el.style.fontWeight === "600" || Number(el.style.fontWeight) >= 600)) {
      return "bf:";
    }
    return "";
  }

  function extractFontPrefixFromDomNode(node) {
    if (!node || node.nodeType !== 1) return "";
    const direct = fontPrefixOfSingleElement(node);
    if (direct) return direct;
    const kids = node.children ? Array.from(node.children) : [];
    for (const child of kids) {
      if (isBlockedHoverNode(child) || (child.classList && child.classList.contains("mspace"))) continue;
      const p = extractFontPrefixFromDomNode(child);
      if (p) return p;
      if ((child.textContent || "").trim()) break;
    }
    return "";
  }

  function extractFontPrefixFromDomSlice(slice) {
    if (!Array.isArray(slice) || slice.length === 0) return "";
    for (const node of slice) {
      if (!node || node.nodeType !== 1) continue;
      if (isBlockedHoverNode(node)) continue;
      const p = extractFontPrefixFromDomNode(node);
      if (p) return p;
      if ((node.textContent || "").trim()) break;
    }
    return "";
  }

  function isRefTargetContainer(node) {
    return node && node.nodeType === 1 &&
      !node.classList.contains("cadmo-ref") &&
      !node.classList.contains("cadmo-sym") &&
      !(node.hasAttribute && node.hasAttribute("data-cadmo-key")) &&
      !node.classList.contains("cadmo-mtext");
  }

  function isStructuralOfflineContainer(node) {
    if (!node || node.nodeType !== 1) return false;
    if (isBlockedHoverNode(node)) return false;
    if (fontPrefixOfSingleElement(node)) return false;
    const cl = node.classList;
    if (cl && (cl.contains("cadmo-op") || cl.contains("cadmo-msym") || cl.contains("cadmo-ref") || cl.contains("cadmo-sym"))) {
      return false;
    }
    if (node.tagName === "VAR") return false;
    return true;
  }

  function wrapSiblingSlice(parent, sliceNodes, candidates, tokenKey = null) {
    if (!sliceNodes || sliceNodes.length === 0) return;
    if (hasBlockedHoverAncestor(parent)) return;
    const span = document.createElement("span");
    span.className = "cadmo-ref";
    const labelText = sliceNodes.map((n) => n.textContent || "").join("");
    parent.insertBefore(span, sliceNodes[0]);
    for (const n of sliceNodes) span.appendChild(n);
    attachInteractiveToken(span, candidates, labelText, tokenKey);
  }

  function annotateOfflineMathContainer(container, scope) {
    if (!container || !scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    if (isBlockedHoverNode(container) || hasBlockedHoverAncestor(container)) return;
    const children = Array.from(container.childNodes);
    let i = 0;
    while (i < children.length) {
      const node = children[i];
      if (node.nodeType !== 1 || !isRefTargetContainer(node) || isBlockedHoverNode(node)) {
        i += 1;
        continue;
      }

      // Skip splitting multi-letter bare <var> runs unless the entire run matches a symbol
      let varRunEnd = i;
      if (node.tagName === "VAR") {
        while (
          varRunEnd + 1 < children.length &&
          children[varRunEnd + 1].nodeType === 1 &&
          children[varRunEnd + 1].tagName === "VAR"
        ) {
          varRunEnd += 1;
        }
      }
      const isBareVarRun = node.tagName === "VAR" && varRunEnd > i;

      let matched = false;
      const maxEnd = Math.min(children.length - 1, i + 7);
      for (let end = maxEnd; end >= i; end--) {
        if (isBareVarRun && end < varRunEnd) continue;
        let validSlice = true;
        for (let k = i; k <= end; k++) {
          const cur = children[k];
          if (cur.nodeType !== 1 || !isRefTargetContainer(cur)) {
            validSlice = false;
            break;
          }
          if (isBlockedHoverNode(cur)) {
            const allowTrailingScript = k > i && (cur.tagName === "SUP" || cur.tagName === "SUB");
            if (!allowTrailingScript) {
              validSlice = false;
              break;
            }
          }
        }
        if (!validSlice) continue;

        // Do not peel base alone when immediately followed by SUB or prime (e.g. R_MAC, x_1, H'')
        if (
          end + 1 < children.length &&
          children[end + 1].nodeType === 1 &&
          (children[end + 1].tagName === "SUB" || children[end + 1].classList.contains("cadmo-prime")) &&
          (isSubAtomEl(children[end]) || children[end].tagName === "SUB")
        ) {
          continue;
        }

        const slice = children.slice(i, end + 1);
        const rawText = slice.map((n) => n.textContent || "").join("");
        const domPrefix = extractFontPrefixFromDomSlice(slice);
        const norm = normalizeMathToken(rawText, domPrefix);
        if (!isNonHoverableToken(norm)) {
          const candidates = resolveTokenCandidates(scope, norm);
          if (candidates && candidates.length > 0) {
            wrapSiblingSlice(container, slice, candidates, norm);
            i = end + 1;
            matched = true;
            break;
          }
        }
      }

      if (matched) continue;

      if (isBareVarRun) {
        // Multi-letter identifier like un-escaped `uniform`: skip whole run without entering SUB
        if (varRunEnd + 1 < children.length && children[varRunEnd + 1].tagName === "SUB") {
          i = varRunEnd + 2;
        } else {
          i = varRunEnd + 1;
        }
        continue;
      }

      if (isStructuralOfflineContainer(node)) {
        annotateOfflineMathContainer(node, scope);
      }
      i += 1;
    }
  }

  function annotateKatexBase(baseEl, scope) {
    if (!baseEl || isBlockedHoverNode(baseEl) || hasBlockedHoverAncestor(baseEl)) return;
    const items = Array.from(baseEl.children).filter(
      (el) => el.classList &&
        !el.classList.contains("cadmo-ref") &&
        !el.classList.contains("mspace") &&
        !(el.hasAttribute && el.hasAttribute("data-cadmo-key"))
    );
    let i = 0;
    while (i < items.length) {
      if (isBlockedHoverNode(items[i])) {
        i += 1;
        continue;
      }
      let matched = false;
      const maxEnd = Math.min(items.length - 1, i + 6);
      for (let end = maxEnd; end >= i; end--) {
        const slice = items.slice(i, end + 1);
        if (slice.some((el, idx) =>
          isBlockedHoverNode(el) && !(idx > 0 && el.classList && el.classList.contains("msupsub"))
        )) continue;
        const domPrefix = extractFontPrefixFromDomSlice(slice);
        const norm = normalizeMathToken(slice.map((el) => el.textContent || "").join(""), domPrefix);
        if (!isNonHoverableToken(norm)) {
          const candidates = resolveTokenCandidates(scope, norm);
          if (candidates && candidates.length > 0) {
            wrapSiblingSlice(baseEl, slice, candidates, norm);
            i = end + 1;
            matched = true;
            break;
          }
        }
      }
      if (!matched) {
        const cur = items[i];
        if (!isBlockedHoverNode(cur)) {
          // Handle wrapper .mord containing base + superscript-only .msupsub (e.g. R^n, \mathbf{G}^2)
          if (
            cur.classList &&
            cur.classList.contains("mord") &&
            !fontPrefixOfSingleElement(cur) &&
            cur.children &&
            cur.children.length > 0 &&
            !(cur.querySelector && cur.querySelector(".msupsub .vlist-t2"))
          ) {
            const hasDirectScript = Array.from(cur.children).some((c) => c.classList && c.classList.contains("msupsub"));
            if (hasDirectScript) {
              annotateKatexBase(cur, scope);
            }
          }
          if (cur.querySelectorAll) {
            const fracContainers = cur.querySelectorAll(".mfrac");
            fracContainers.forEach((sc) => {
              if (!hasBlockedHoverAncestor(sc)) annotateKatexMath(sc, scope);
            });
          }
        }
        i += 1;
      }
    }
  }

  function annotateKatexMath(root, scope) {
    if (!root || !scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    if (isBlockedHoverNode(root) || hasBlockedHoverAncestor(root)) return;
    const bases = root.querySelectorAll ? root.querySelectorAll(".base") : [];
    if (bases.length > 0) {
      bases.forEach((b) => {
        if (!hasBlockedHoverAncestor(b)) annotateKatexBase(b, scope);
      });
    } else {
      annotateKatexBase(root, scope);
    }
  }

  function annotateMathReferences(mathEl, scope) {
    if (!mathEl) return;
    if (mathEl.querySelectorAll) {
      const pinnedNodes = mathEl.querySelectorAll("[data-cadmo-key]");
      pinnedNodes.forEach((pEl) => {
        if (pEl.classList.contains("cadmo-ref") || pEl.classList.contains("cadmo-sym") || hasBlockedHoverAncestor(pEl)) return;
        const pKey = pEl.getAttribute("data-cadmo-key");
        if (!pKey) return;
        const ins = inspectorByKey.get(pKey);
        if (ins) {
          pEl.classList.add("cadmo-ref");
          attachInteractiveToken(pEl, [ins], pEl.textContent || ins.display, `key:${pKey}`);
        }
      });
    }
    if (!scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    const katexHtml = mathEl.querySelector ? mathEl.querySelector(".katex-html") : null;
    if (katexHtml) {
      annotateKatexMath(katexHtml, scope);
    } else {
      annotateOfflineMathContainer(mathEl, scope);
    }
  }

  function normalizeMathLatex(tex) {
    return String(tex || "")
      .replace(/(\\(?:left|bigl|Bigl)?\[)(?:\\[,;:]|\s)+([^\[\]\n]*?)(?:\\[,;:]|\s)+(\\(?:right|bigr|Bigr)?\])/g, "$1$2$3")
      .replace(/\[(?:\\[,;:])+\s*([^\[\]\n]*?)\s*(?:\\[,;:])+\]/g, "[$1]")
      .replace(/\[\s+([A-Za-z0-9_{}\\]+?)\s*\]/g, "[$1]")
      .replace(/\[\s*([A-Za-z0-9_{}\\]+?)\s+\]/g, "[$1]");
  }

  function renderMathSpan(tex, displayMode = false, scope = null) {
    const cleanTex = normalizeMathLatex(tex);
    const el = document.createElement("span");
    el.className = displayMode ? "cadmo-display-math" : "cadmo-math";
    el.dataset.latex = cleanTex;
    if (window.katex && typeof window.katex.render === "function") {
      try {
        window.katex.render(cleanTex, el, { displayMode, throwOnError: false });
        annotateMathReferences(el, scope);
        return el;
      } catch (_) {
        /* fallback below */
      }
    }
    el.appendChild(renderMathNodes(cleanTex));
    annotateMathReferences(el, scope);
    return el;
  }

  function h(tag, attrs = {}, ...children) {
    const el = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
      if (v === null || v === undefined || v === false) continue;
      if (k === "class") el.className = v;
      else if (k === "dataset") Object.assign(el.dataset, v);
      else if (k.startsWith("on") && typeof v === "function") {
        el.addEventListener(k.slice(2).toLowerCase(), v);
      } else if (v === true) {
        el.setAttribute(k, "");
      } else {
        el.setAttribute(k, String(v));
      }
    }
    for (const child of children.flat()) {
      if (child === null || child === undefined || child === false) continue;
      if (typeof child === "string") el.appendChild(document.createTextNode(child));
      else el.appendChild(child);
    }
    return el;
  }

  function formatProseDashes(str) {
    return String(str || "")
      .replace(/---/g, "\u2014")
      .replace(/(?<![-<])--(?!-|->)/g, "\u2013")
      .replace(/([A-Za-z0-9.)])~(?=[A-Za-z0-9(\\$])/g, "$1\u00A0");
  }

  function renderProseSegment(seg) {
    const frag = document.createDocumentFragment();
    if (!seg) return frag;
    const text = String(seg);
    const re = /\*\*([^\s*\n](?:[^*\n]*?[^\s*\n])?)\*\*|(?<![\w\\*])\*([^\s*\n](?:[^*\n]*?[^\s*\n])?)\*(?![\w*])/g;
    let last = 0;
    let m;
    while ((m = re.exec(text)) !== null) {
      if (m.index > last) {
        frag.appendChild(document.createTextNode(formatProseDashes(text.slice(last, m.index))));
      }
      if (m[1] !== undefined) {
        frag.appendChild(h("strong", {}, formatProseDashes(m[1])));
      } else if (m[2] !== undefined) {
        frag.appendChild(h("em", {}, formatProseDashes(m[2])));
      }
      last = re.lastIndex;
    }
    if (last < text.length) {
      frag.appendChild(document.createTextNode(formatProseDashes(text.slice(last))));
    }
    return frag;
  }

  function renderMixedText(segOrStr, scope = null) {
    const frag = document.createDocumentFragment();
    if (!segOrStr) return frag;
    const text = String(segOrStr);
    const re = /\\\(([\s\S]*?)\\\)|\\\[([\s\S]*?)\\\]|\$\$([\s\S]*?)\$\$|(?<!\\)\$([^$\n]+?)(?<!\\)\$|\\\$/g;
    let last = 0;
    let m;
    while ((m = re.exec(text)) !== null) {
      if (m.index > last) {
        let chunk = text.slice(last, m.index);
        if (m[0] !== "\\$") chunk = chunk.replace(/([A-Za-z0-9.)])~$/, "$1\u00A0");
        frag.appendChild(renderProseSegment(chunk));
      }
      if (m[0] === "\\$") {
        frag.appendChild(document.createTextNode("$"));
      } else if (m[1] !== undefined) {
        frag.appendChild(renderMathSpan(m[1], false, scope));
      } else if (m[2] !== undefined) {
        frag.appendChild(renderMathSpan(m[2], true, scope));
      } else if (m[3] !== undefined) {
        frag.appendChild(renderMathSpan(m[3], true, scope));
      } else if (m[4] !== undefined) {
        frag.appendChild(renderMathSpan(m[4], false, scope));
      }
      last = re.lastIndex;
    }
    if (last < text.length) frag.appendChild(renderProseSegment(text.slice(last)));
    return frag;
  }

  function getTrustLevel(obj, variantObj = null) {
    if (!obj || typeof obj !== "object") return null;
    const t = (variantObj && typeof variantObj === "object" ? (variantObj.trust || variantObj.proseTrust) : null) ||
      obj.trust || obj.proseTrust || null;
    if (
      t === "kernelFormula" ||
      t === "kernelProvedClaim" ||
      t === "typedRef" ||
      t === "intuitionGloss" ||
      t === "authorGloss"
    ) {
      return t;
    }
    return null;
  }

  function trustClassAndTitle(trust) {
    if (!trust) return null;
    if (trust === "intuitionGloss" || trust === "authorGloss") {
      return {
        cls: "cadmo-trust-gloss",
        title: state.mode === "auditor"
          ? (trust === "authorGloss" ? "Authorial motivation (non-claiming)" : "Authorial gloss (intuition)")
          : ""
      };
    }
    const titles = {
      kernelFormula: "Kernel-verified formula",
      kernelProvedClaim: "Kernel-verified claim",
      typedRef: "Kernel-verified typed reference"
    };
    return {
      cls: "cadmo-trust-kernel",
      title: state.mode === "auditor" ? (titles[trust] || "Kernel-verified") : ""
    };
  }

  function applyInlineTrust(node, inl, variantObj = null) {
    const trust = getTrustLevel(inl, variantObj);
    const info = trustClassAndTitle(trust);
    if (!info) return node;
    if (node && node.nodeType === 1) {
      node.classList.add(info.cls);
      node.setAttribute("data-trust", trust);
      if (info.title && !node.getAttribute("title")) node.setAttribute("title", info.title);
      return node;
    }
    return h("span", {
      class: info.cls,
      "data-trust": trust,
      title: info.title || null
    }, node);
  }

  function renderInline(inl, scope = null) {
    if (!inl || typeof inl !== "object") return document.createTextNode("");
    if (inl.text !== undefined) {
      const val = typeof inl.text === "string" ? inl.text : inl.text.value;
      return applyInlineTrust(renderMixedText(val || "", scope), inl, inl.text);
    }
    if (inl.emph !== undefined) {
      const val = typeof inl.emph === "string" ? inl.emph : inl.emph.value;
      return applyInlineTrust(h("em", {}, renderMixedText(val || "", scope)), inl, inl.emph);
    }
    if (inl.inlineMath !== undefined) {
      const obj = inl.inlineMath;
      const tex = typeof obj === "string" ? obj : obj.latex;
      const dataKey = (typeof obj === "object" && obj ? (obj.dataKey || obj["data-cadmo-key"]) : null) ||
        inl.dataKey || inl["data-cadmo-key"] || null;
      const ins = dataKey ? inspectorByKey.get(dataKey) : null;
      const span = renderMathSpan(tex || "", false, ins ? null : scope);
      if (dataKey) span.setAttribute("data-cadmo-key", dataKey);
      if (ins && !hasBlockedHoverAncestor(span)) {
        span.classList.add("cadmo-ref");
        attachInteractiveToken(span, [ins], span.textContent || ins.display, `key:${dataKey}`);
      }
      return applyInlineTrust(span, inl, obj);
    }
    if (inl.displayMath !== undefined) {
      const obj = inl.displayMath;
      const tex = typeof obj === "string" ? obj : obj.latex;
      const punct = typeof obj === "object" && obj.punct ? obj.punct : "";
      const dataKey = (typeof obj === "object" && obj ? (obj.dataKey || obj["data-cadmo-key"]) : null) ||
        inl.dataKey || inl["data-cadmo-key"] || null;
      const ins = dataKey ? inspectorByKey.get(dataKey) : null;
      const span = renderMathSpan((tex || "") + (punct ? "\\," + punct : ""), true, ins ? null : scope);
      if (dataKey) span.setAttribute("data-cadmo-key", dataKey);
      if (ins && !hasBlockedHoverAncestor(span)) {
        span.classList.add("cadmo-ref");
        attachInteractiveToken(span, [ins], span.textContent || ins.display, `key:${dataKey}`);
      }
      return applyInlineTrust(span, inl, obj);
    }
    if (inl.symbol !== undefined) {
      const sym = inl.symbol;
      const pinnedKey = sym.dataKey || sym["data-cadmo-key"] || inl.dataKey || inl["data-cadmo-key"] || sym.key;
      const ins = inspectorByKey.get(pinnedKey) || inspectorByKey.get(sym.key);
      const isSelected = state.inspector && state.inspector.type === "symbol" &&
        state.inspector.item.key === (ins ? ins.key : pinnedKey);
      const btn = h("button", {
        type: "button",
        class: sym.isMath ? "cadmo-sym" : "cadmo-sym cadmo-sym-prose",
        "data-cadmo-key": pinnedKey || "",
        "aria-pressed": isSelected ? "true" : "false"
      }, sym.isMath ? renderMathSpan(sym.display, false, null) : sym.display);
      if (ins) {
        attachInteractiveToken(btn, [ins], sym.display, `key:${ins.key}`);
      } else {
        btn.addEventListener("click", () => {
          state.inspector = null;
          renderMarginOnly();
        });
      }
      return applyInlineTrust(btn, inl, sym);
    }
    if (inl.citation !== undefined) {
      const c = inl.citation;
      return applyInlineTrust(h("span", { title: c.detail || "" }, `[${c.label}]`), inl, c);
    }
    return document.createTextNode("");
  }

  function inlineVisibleTailChar(inl) {
    if (!inl || typeof inl !== "object") return "";
    if (inl.text !== undefined) {
      const v = typeof inl.text === "string" ? inl.text : inl.text.value;
      return v ? v.slice(-1) : "";
    }
    if (inl.emph !== undefined) {
      const v = typeof inl.emph === "string" ? inl.emph : inl.emph.value;
      return v ? v.slice(-1) : "";
    }
    if (inl.inlineMath !== undefined) {
      const obj = inl.inlineMath;
      const t = typeof obj === "string" ? obj : (obj && obj.latex ? obj.latex : "");
      return t ? t.trim().slice(-1) : "";
    }
    if (inl.displayMath !== undefined) {
      const obj = inl.displayMath;
      return typeof obj === "object" && obj && obj.punct ? String(obj.punct).slice(-1) : "";
    }
    if (inl.symbol !== undefined) {
      return inl.symbol && inl.symbol.display ? String(inl.symbol.display).slice(-1) : "";
    }
    if (inl.citation !== undefined) return "]";
    return "";
  }

  function inlineVisibleHeadText(inl) {
    if (!inl || typeof inl !== "object") return "";
    if (inl.text !== undefined) {
      return String((typeof inl.text === "string" ? inl.text : inl.text.value) || "");
    }
    if (inl.emph !== undefined) {
      return String((typeof inl.emph === "string" ? inl.emph : inl.emph.value) || "");
    }
    return "";
  }

  function renderInlines(arr, scope = null) {
    const frag = document.createDocumentFragment();
    let prevTail = "";
    for (const item of arr || []) {
      const head = inlineVisibleHeadText(item);
      if (
        (prevTail === "." || prevTail === "!" || prevTail === "?") &&
        head &&
        /^[A-Za-z]/.test(head)
      ) {
        frag.appendChild(document.createTextNode(" "));
      }
      frag.appendChild(renderInline(item, scope));
      const tail = inlineVisibleTailChar(item);
      if (tail) prevTail = tail;
    }
    return frag;
  }

  function projectNodes(nodes) {
    if (!Array.isArray(nodes)) return [];
    if (state.mode === "auditor") return nodes;
    const out = [];
    for (const n of nodes) {
      if (n && n.kind === "step" && n.isWrapper) {
        if (Array.isArray(n.children) && n.children.length > 0) {
          out.push(...projectNodes(n.children));
        }
      } else if (n) {
        out.push(n);
      }
    }
    return out;
  }

  function paperVisibleChildren(rawNodes) {
    const vis = projectNodes(rawNodes || []);
    if (state.mode === "auditor") return vis;
    if (vis.length === 0) return [];
    // Omit a Paper-mode disclosure toggle when the only visible child is a single routineReceipt
    if (vis.length === 1 && vis[0] && vis[0].kind === "routineReceipt") return [];
    return vis;
  }

  function hasVisibleDiagramHtml(htmlStr) {
    return stripEmbeddedStyles(htmlStr || "").trim().length > 0;
  }

  function fitDiagrams(root = (typeof document !== "undefined" ? document : null)) {
    if (!root || typeof root.querySelectorAll !== "function") return;
    let bodies;
    try {
      bodies = Array.from(root.querySelectorAll(".cadmo-diagram-body"));
    } catch (_) {
      return;
    }
    for (const body of bodies) {
      if (!body || typeof body.querySelectorAll !== "function") continue;
      const card = typeof body.closest === "function" ? body.closest(".cadmo-diagram") : null;
      if (card && card.tagName === "DETAILS" && !card.open) continue;
      const ccw = typeof body.querySelector === "function" ? body.querySelector("details.ccw") : null;
      if (ccw && !ccw.open) continue;
      const bodyW = Number(body.clientWidth || 0);
      if (!(bodyW > 24)) continue;
      const surface = typeof body.querySelector === "function" ? body.querySelector(".cc-surface") : null;
      const surfW = surface ? Number(surface.clientWidth || 0) : 0;
      const availW = surfW > 24
        ? Math.max(120, Math.floor(surfW - 20))
        : Math.max(120, Math.floor(bodyW - 16));

      const comps = Array.from(body.querySelectorAll(".cc-comparison"));
      for (const comp of comps) {
        if (!comp || !comp.style) continue;
        let wrap = comp.parentElement;
        if (!wrap || !wrap.classList || !wrap.classList.contains("cadmo-diag-scale-wrap")) {
          wrap = document.createElement("div");
          wrap.className = "cadmo-diag-scale-wrap";
          if (comp.parentNode) {
            comp.parentNode.insertBefore(wrap, comp);
            wrap.appendChild(comp);
          }
        }
        comp.style.transform = "";
        comp.style.transformOrigin = "";
        comp.style.width = "";
        comp.style.maxInlineSize = "";
        comp.style.flexDirection = "";
        comp.style.flexWrap = "";
        const cardsEls = typeof comp.querySelectorAll === "function" ? Array.from(comp.querySelectorAll(".cc-cards")) : [];
        for (const c of cardsEls) {
          if (c && c.style) {
            c.style.flexWrap = "";
            c.style.maxInlineSize = "";
          }
        }
        if (wrap && wrap.style) {
          wrap.style.width = "";
          wrap.style.height = "";
          wrap.style.marginInline = "auto";
          wrap.style.overflow = "visible";
        }

        let natW = Math.ceil(comp.scrollWidth || 0);
        if (!(natW > 0)) continue;
        if (natW > availW + 1) {
          if (availW / natW < 0.55) {
            if (cardsEls.length > 0) {
              for (const c of cardsEls) {
                if (c && c.style) {
                  c.style.flexWrap = "wrap";
                  c.style.maxInlineSize = availW + "px";
                }
              }
            }
            if (comp.children && comp.children.length > 1) {
              comp.style.flexDirection = "column";
            }
            natW = Math.ceil(comp.scrollWidth || 0);
          }
          if (natW > availW + 1) {
            comp.style.width = natW + "px";
            comp.style.maxInlineSize = "none";
            const measuredW = Math.max(natW, Math.ceil(comp.scrollWidth || natW));
            const measuredH = Math.ceil(comp.scrollHeight || 0);
            const scale = Math.min(1, Math.max(0.2, availW / measuredW));
            comp.style.width = measuredW + "px";
            comp.style.transformOrigin = "top left";
            comp.style.transform = `scale(${scale})`;
            if (wrap && wrap.style) {
              wrap.style.width = Math.min(availW, Math.ceil(measuredW * scale)) + "px";
              if (measuredH > 0) wrap.style.height = Math.ceil(measuredH * scale) + "px";
              wrap.style.marginInline = "auto";
              wrap.style.overflow = "visible";
            }
          }
        } else if (wrap && wrap.style) {
          wrap.style.width = "";
          wrap.style.height = "";
          wrap.style.marginInline = "auto";
        }
      }
    }
  }

  function scheduleFitDiagrams(root = (typeof document !== "undefined" ? document : null)) {
    if (typeof window !== "undefined" && typeof window.requestAnimationFrame === "function") {
      window.requestAnimationFrame(() => fitDiagrams(root));
    } else {
      fitDiagrams(root);
    }
  }

  function renderCollapsibleDiagram(htmlStr, cls, summaryLabel, defaultOpen = false) {
    const cleanHtml = stripEmbeddedStyles(htmlStr || "").trim();
    if (!cleanHtml) return null;
    const bodyEl = h("div", { class: "cadmo-diagram-body" });
    bodyEl.innerHTML = cleanHtml;
    const det = h("details", {
      class: `cadmo-diagram ${cls}`,
      open: defaultOpen ? true : null
    },
      h("summary", {}, summaryLabel),
      bodyEl
    );
    if (typeof det.addEventListener === "function") {
      det.addEventListener("toggle", () => {
        if (det.open) {
          if (typeof bodyEl.querySelectorAll === "function") {
            bodyEl.querySelectorAll("details.ccw").forEach((cc) => { cc.open = true; });
          }
          scheduleFitDiagrams(det);
        }
      });
    }
    return det;
  }

  function collectAllExpandableIds(nodes, out = []) {
    for (const n of projectNodes(nodes || [])) {
      if (n.kind === "step") {
        const vis = paperVisibleChildren(n.children || []);
        if (vis.length > 0) {
          out.push(n.id);
          collectAllExpandableIds(vis, out);
        }
      } else if (n.kind === "calcChain") {
        (n.steps || []).forEach((s, idx) => {
          const vis = paperVisibleChildren(s.justification || s.children || []);
          if (vis.length > 0) {
            out.push(`${n.id}-s${idx}`);
            collectAllExpandableIds(vis, out);
          }
        });
      } else if (n.kind === "routineReceipt") {
        const vis = paperVisibleChildren(n.details || []);
        if (vis.length > 0) {
          out.push(n.id);
          collectAllExpandableIds(vis, out);
        }
      }
    }
    return out;
  }

  function renderGoalButton(goal, label) {
    if (!goal) return null;
    const active = state.inspector && state.inspector.type === "goal" &&
      state.inspector.goal === goal;
    return h("button", {
      type: "button",
      class: "cadmo-goal-btn",
      "aria-pressed": active ? "true" : "false",
      title: "Show checked proof state in margin",
      onClick: () => {
        state.inspector = { type: "goal", goal, label };
        renderAll();
      }
    }, "⊢");
  }

  const BOX_KIND_LABELS = {
    attackGame: "Attack Game",
    hybrid: "Hybrid",
    reduction: "Reduction",
    distinguisher: "Distinguisher",
    algorithm: "Algorithm"
  };

  function boxKindLabel(boxKind) {
    return BOX_KIND_LABELS[boxKind] || boxKind || "Algorithm";
  }

  function renderPseudocodeLines(lines, scope = null) {
    if (!Array.isArray(lines) || lines.length === 0) return null;
    return h("div", { class: "cadmo-pseudocode-lines" },
      ...lines.map((ln) => {
        const indent = Math.max(0, Number((ln && ln.indent) || 0));
        const inlines = (ln && Array.isArray(ln.inlines)) ? ln.inlines : [];
        const lineEl = h("div", {
          class: "cadmo-pseudocode-line",
          "data-indent": String(indent),
          style: indent > 0 ? `padding-left: calc(${indent} * 1.4em)` : null
        }, renderInlines(inlines, scope));
        if (indent > 0 && lineEl.style) {
          lineEl.style.paddingLeft = `calc(${indent} * 1.4em)`;
        }
        return lineEl;
      })
    );
  }

  function renderPseudocodeBox(node, scope = null) {
    if (!node || typeof node !== "object") return null;
    const boxKind = node.boxKind || "algorithm";
    const titleStr = typeof node.title === "string" ? node.title.trim() : "";
    const originTag = node.originDecl ? h("span", { class: "cadmo-origin-tag" }, node.originDecl) : null;
    const goalBtn = renderGoalButton(node.goal, titleStr || node.originDecl || "Pseudocode box");
    const hasMeta = !!(originTag || goalBtn);
    return h("figure", {
      class: `cadmo-pseudocode-box cadmo-pbox-${boxKind}`,
      "data-node-id": node.id || null,
      "data-box-kind": boxKind
    },
      h("figcaption", { class: "cadmo-pbox-head" },
        h("div", { class: "cadmo-pbox-title-group" },
          h("span", { class: "cadmo-pbox-kind" }, boxKindLabel(boxKind)),
          titleStr ? h("span", { class: "cadmo-pbox-title" }, renderMixedText(titleStr, scope)) : null
        ),
        hasMeta ? h("div", { class: "cadmo-pbox-meta" }, originTag, goalBtn) : null
      ),
      renderPseudocodeLines(node.lines || [], scope)
    );
  }

  function renderPreludeBlock(p, scope = null, opts = {}) {
    if (!p || typeof p !== "object") return null;
    const kind = p.kind || "definition";
    const labelStr = typeof p.label === "string" ? formatProseDashes(p.label.trim()) : "";
    const titleStr = typeof p.title === "string" ? p.title.trim() : "";
    const declKey = typeof p.declKey === "string" && p.declKey.trim() ? p.declKey.trim() : null;
    const declIns = declKey ? inspectorByKey.get(declKey) : null;
    const entryDiagNorm = opts && typeof opts.entryDiagramHtml === "string"
      ? stripEmbeddedStyles(opts.entryDiagramHtml).trim()
      : "";
    const pDiagNorm = stripEmbeddedStyles(p.diagramHtml || "").trim();
    const skipDiagram = (kind === "setting") ||
      (kind === "construction" && !!entryDiagNorm && pDiagNorm === entryDiagNorm);

    if (kind === "setting" || kind === "motivation") {
      const bodyParas = Array.isArray(p.body) ? p.body : [];
      const leadSpan = labelStr
        ? h("span", { class: "cadmo-ambient-label" }, /[.!?]$/.test(labelStr) ? `${labelStr} ` : `${labelStr}. `)
        : null;
      const paras = bodyParas.length > 0
        ? bodyParas.map((para, idx) =>
            h("p", {}, idx === 0 ? leadSpan : null, renderInlines(para, scope))
          )
        : (titleStr ? [h("p", {}, leadSpan, renderMixedText(titleStr, scope))] : []);
      if (paras.length === 0) return null;
      const attrs = {
        class: `cadmo-prelude cadmo-prelude-${kind}` + (kind === "motivation" ? " cadmo-trust-gloss" : ""),
        id: p.id || null,
        "data-prelude-kind": kind
      };
      if (kind === "motivation") {
        attrs["data-trust"] = "authorGloss";
        if (state.mode === "auditor") attrs.title = "Authorial motivation (non-claiming)";
      }
      const diagEl = skipDiagram ? null : renderCollapsibleDiagram(p.diagramHtml, "cadmo-prelude-diagram", "System figure", false);
      return h("section", attrs, h("div", { class: "cadmo-prelude-body" }, ...paras), diagEl);
    }

    let inspectBtn = null;
    if (declKey) {
      inspectBtn = h("button", {
        type: "button",
        class: "cadmo-prelude-inspect cadmo-action-link",
        "data-cadmo-key": declKey
      }, "Inspect");
      if (declIns) {
        attachInteractiveToken(
          inspectBtn,
          [declIns],
          titleStr || labelStr || declIns.display || declKey,
          `key:${declIns.key}`
        );
      } else {
        inspectBtn.disabled = true;
        inspectBtn.title = declKey;
      }
    }

    const hasHeading = !!(labelStr || titleStr || inspectBtn);
    const headEl = hasHeading
      ? h("div", { class: "cadmo-prelude-head" },
          h("div", { class: "cadmo-prelude-heading" },
            labelStr ? h("span", { class: "cadmo-prelude-label" }, labelStr) : null,
            titleStr
              ? h("span", { class: "cadmo-prelude-title" },
                  labelStr ? " (" : null,
                  renderMixedText(titleStr, scope),
                  labelStr ? ")" : null
                )
              : null
          ),
          inspectBtn
        )
      : null;

    const bodyParas = Array.isArray(p.body) ? p.body : [];
    const bodyEl = bodyParas.length > 0
      ? h("div", { class: "cadmo-prelude-body" },
          ...bodyParas.map((para) => h("p", {}, renderInlines(para, scope)))
        )
      : null;

    const headers = Array.isArray(p.headers) ? p.headers : [];
    const theadEl = headers.length > 0
      ? h("thead", {},
          h("tr", {},
            ...headers.map((hd) =>
              h("th", { scope: "col" }, Array.isArray(hd) ? renderInlines(hd, scope) : renderMixedText(String(hd || ""), scope))
            )
          )
        )
      : null;
    const rows = Array.isArray(p.rows) ? p.rows : [];
    const rowsEl = rows.length > 0
      ? h("table", { class: "cadmo-prelude-table" },
          theadEl,
          h("tbody", {},
            ...rows.map((r) =>
              h("tr", {},
                h("th", { scope: "row", class: "cadmo-prelude-row-left" }, renderInlines((r && r.left) || [], scope)),
                h("td", { class: "cadmo-prelude-row-right" }, renderInlines((r && r.right) || [], scope))
              )
            )
          )
        )
      : null;

    const linesEl = renderPseudocodeLines(p.lines || [], scope);
    const diagEl = skipDiagram ? null : renderCollapsibleDiagram(p.diagramHtml, "cadmo-prelude-diagram", "System figure", false);

    return h("section", {
      class: `cadmo-prelude cadmo-prelude-${kind}`,
      id: p.id || null,
      "data-prelude-kind": kind
    }, headEl, bodyEl, rowsEl, linesEl, diagEl);
  }

  function renderSectionPreludes(entry, scope = null) {
    if (!entry || !Array.isArray(entry.sectionPreludes) || entry.sectionPreludes.length === 0) return null;
    const opts = { entryDiagramHtml: entry.diagramHtml || "" };
    const blocks = entry.sectionPreludes.map((p) => renderPreludeBlock(p, scope, opts)).filter(Boolean);
    if (blocks.length === 0) return null;
    return h("div", { class: "cadmo-section-preludes" }, ...blocks);
  }

  /* ------------------------------------------------------------------------
     Flowing paragraph proof renderer: consecutive `step` siblings flow inline
     inside natural `<p class="cadmo-proof-para">` paragraphs (just like
     Maurer–Renner / Kerodon), with quiet inline superscript ⊕ / ⊖ triggers.
     Only when a sentence is expanded does an indented `.cadmo-expansion`
     open right below it!
     ------------------------------------------------------------------------ */
  function renderProofFlow(rawNodes, opts = {}) {
    const { leadIn = null, appendQed = false, depth = 0, scope = null } = opts;
    const nodes = projectNodes(rawNodes || []);
    const out = [];
    let paraChildren = [];
    let usedLeadIn = false;

    function flushPara(isLast = false) {
      if (paraChildren.length === 0) return;
      const p = h("p", { class: "cadmo-proof-para" }, ...paraChildren);
      if (isLast && appendQed) {
        p.appendChild(h("span", { class: "cadmo-qed", "aria-hidden": "true" }, "□"));
      }
      out.push(p);
      paraChildren = [];
    }

    function ensureLeadIn() {
      if (leadIn && !usedLeadIn) {
        paraChildren.push(h("span", { class: "cadmo-proof-lead" }, leadIn));
        paraChildren.push(" ");
        usedLeadIn = true;
      }
    }

    function emitSentence(sentEl, childrenEl = null) {
      if (depth > 0) {
        flushPara(false);
        const kids = [];
        if (leadIn && !usedLeadIn) {
          kids.push(h("span", { class: "cadmo-proof-lead" }, leadIn));
          kids.push(" ");
          usedLeadIn = true;
        }
        kids.push(sentEl);
        out.push(h("div", { class: "cadmo-expanded-step" }, ...kids));
        if (childrenEl) out.push(childrenEl);
      } else {
        ensureLeadIn();
        if (paraChildren.length > 0 && paraChildren[paraChildren.length - 1] !== " ") {
          paraChildren.push(" ");
        }
        paraChildren.push(sentEl);
        if (childrenEl) {
          flushPara(false);
          out.push(childrenEl);
        }
      }
    }

    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      if (!node) continue;

      if (node.kind === "figure") {
        flushPara(false);
        const cleanHtml = stripEmbeddedStyles(node.html || "").trim();
        const capArr = Array.isArray(node.caption) ? node.caption : [];
        const capStr = typeof node.caption === "string" ? node.caption.trim() : "";
        const hasCaption = capArr.length > 0 || capStr.length > 0;
        if (!cleanHtml && !hasCaption) continue;
        const bodyDiv = h("div", { class: "cadmo-diagram-body" });
        bodyDiv.innerHTML = cleanHtml;
        out.push(
          h("figure", {
            class: "cadmo-diagram cadmo-figure",
            "data-node-id": node.id || null
          },
            bodyDiv,
            hasCaption
              ? h("figcaption", { class: "cadmo-figure-caption" },
                  capArr.length > 0 ? renderInlines(capArr, scope) : renderMixedText(capStr, scope)
                )
              : null
          )
        );
        continue;
      }

      if (node.kind === "flowNote") {
        flushPara(false);
        const noteText = typeof node.text === "string" ? node.text.trim() : "";
        if (node.placement === "paragraph") {
          if (noteText) {
            ensureLeadIn();
            paraChildren.push(h("span", { class: "cadmo-para-heading" }, renderMixedText(noteText + " ", scope)));
          }
          continue;
        }
        if (noteText) {
          const p = h("p", { class: "cadmo-flow-note" }, renderMixedText(node.text || "", scope));
          out.push(p);
        }
        continue;
      }

      if (node.kind === "pseudocodeBox") {
        if (leadIn && !usedLeadIn) ensureLeadIn();
        flushPara(false);
        const boxEl = renderPseudocodeBox(node, scope);
        if (boxEl) out.push(boxEl);
        continue;
      }

      if (node.kind === "routineReceipt") {
        // In Paper mode at top level, keep pure routine receipts quiet unless there's no other step
        if (state.mode === "paper" && depth === 0 && nodes.length > 1) continue;
        const details = paperVisibleChildren(node.details || []);
        const hasDetails = details.length > 0;
        const isOpen = state.expanded.has(node.id);
        const sent = h("span", { class: "cadmo-sent cadmo-routine" },
          renderMixedText(`By ${node.summary || "routine algebra"}.`, scope),
          hasDetails
            ? h("button", {
                type: "button",
                class: "cadmo-inline-toggle",
                "aria-expanded": isOpen ? "true" : "false",
                onClick: () => toggleId(node.id)
              }, isOpen ? "⊖" : "⊕")
            : null,
          renderGoalButton(node.goal, node.summary || "Routine step")
        );
        const childrenEl = (hasDetails && isOpen)
          ? h("div", { class: "cadmo-expansion cadmo-expanded-children" },
              ...renderProofFlow(details, { depth: depth + 1, scope })
            )
          : null;
        emitSentence(sent, childrenEl);
        continue;
      }

      if (node.kind === "calcChain") {
        if (node.intro && node.intro.length > 0) {
          ensureLeadIn();
          if (paraChildren.length > 0 && paraChildren[paraChildren.length - 1] !== " ") {
            paraChildren.push(" ");
          }
          paraChildren.push(
            h("span", { class: "cadmo-sent" },
              renderInlines(node.intro, scope),
              renderGoalButton(node.goal, "Calculation target")
            )
          );
        } else if (leadIn && !usedLeadIn) {
          ensureLeadIn();
        }
        flushPara(false);
        const calcItems = [];
        const steps = node.steps || [];
        steps.forEach((item, idx) => {
          const st = item.step || {};
          const ch = paperVisibleChildren(item.justification || item.children || []);
          const hasExpandable = ch.length > 0;
          const sid = `${node.id}-s${idx}`;
          const isOpen = state.expanded.has(sid);
          if (idx === 0 && st.lhsLatex) {
            calcItems.push(
              h("div", { class: "cadmo-calc-lhs-line" },
                renderMathSpan(st.lhsLatex || "", false, scope)
              )
            );
          }
          calcItems.push(
            h("div", { class: "cadmo-calc-step-row" },
              h("span", { class: "cadmo-calc-rel" }, renderMathSpan(st.relationLatex || "=", false, scope)),
              h("span", { class: "cadmo-calc-rhs" }, renderMathSpan(st.rhsLatex || "", false, scope)),
              h("span", { class: "cadmo-calc-reason" },
                (st.reason && st.reason.length > 0) ? "(" : null,
                renderInlines(st.reason || [], scope),
                (st.reason && st.reason.length > 0) ? ")" : null,
                hasExpandable
                  ? h("button", {
                      type: "button",
                      class: "cadmo-inline-toggle",
                      "aria-expanded": isOpen ? "true" : "false",
                      title: isOpen ? "Collapse justification" : "Expand justification",
                      onClick: () => toggleId(sid)
                    }, isOpen ? "⊖" : "⊕")
                  : null
              )
            )
          );
          if (hasExpandable && isOpen) {
            calcItems.push(
              h("div", { class: "cadmo-calc-expand-block" },
                h("div", { class: "cadmo-expansion cadmo-expanded-children" },
                  ...renderProofFlow(ch, { depth: depth + 1, scope })
                )
              )
            );
          }
        });
        out.push(h("div", { class: "cadmo-calc" },
          h("div", { class: "cadmo-calc-list" }, ...calcItems)
        ));
        continue;
      }

      // Default: `step` — flows INLINE inside depth-0 paragraph, or as separate block at depth > 0
      if (node.startsParagraph) {
        flushPara(false);
      }
      const children = paperVisibleChildren(node.children || []);
      const hasChildren = children.length > 0;
      const isOpen = state.expanded.has(node.id);
      const toggleBtn = hasChildren
        ? h("button", {
            type: "button",
            class: "cadmo-inline-toggle",
            "aria-expanded": isOpen ? "true" : "false",
            title: isOpen ? "Collapse subproof" : "Expand subproof",
            onClick: () => toggleId(node.id)
          }, isOpen ? "⊖" : "⊕")
        : null;
      const stepTrust = getTrustLevel(node);
      const stepTrustInfo = trustClassAndTitle(stepTrust);
      const trustBadge = (stepTrust === "intuitionGloss" || stepTrust === "authorGloss")
        ? h("span", { class: "cadmo-trust-badge" }, "[gloss]")
        : null;
      const wrapperTag = node.isWrapper ? h("span", { class: "cadmo-wrapper-tag" }, "[wrapper]") : null;
      const originTag = node.originDecl ? h("span", { class: "cadmo-origin-tag" }, node.originDecl) : null;
      const goalBtn = renderGoalButton(node.goal, node.originDecl || "Proof step");
      const leadHeadingStr = typeof node.leadHeading === "string" ? node.leadHeading.trim() : "";
      const leadHeadSpan = leadHeadingStr
        ? h("span", { class: "cadmo-para-heading" }, renderMixedText(leadHeadingStr + " ", scope))
        : null;
      const contentArr = node.content || [];
      const endsWithDisplay = contentArr.length > 0 && contentArr[contentArr.length - 1]?.displayMath !== undefined;
      const sentClass = "cadmo-sent" +
        (node.isWrapper ? " is-wrapper" : "") +
        (stepTrustInfo ? ` ${stepTrustInfo.cls}` : "");
      const sentAttrs = {
        class: sentClass,
        "data-trust": stepTrust || null,
        title: (stepTrustInfo && stepTrustInfo.title) ? stepTrustInfo.title : null
      };
      let sent;
      if (endsWithDisplay) {
        const preInlines = contentArr.slice(0, -1);
        const dispInl = contentArr[contentArr.length - 1];
        sent = h("span", sentAttrs,
          leadHeadSpan,
          renderInlines(preInlines, scope),
          h("span", { class: "cadmo-display-wrap" },
            renderInline(dispInl, scope),
            (toggleBtn || trustBadge || wrapperTag || originTag || goalBtn)
              ? h("span", { class: "cadmo-display-controls" }, toggleBtn, trustBadge, wrapperTag, originTag, goalBtn)
              : null
          )
        );
      } else {
        sent = h("span", sentAttrs,
          leadHeadSpan,
          renderInlines(contentArr, scope),
          toggleBtn,
          trustBadge,
          wrapperTag,
          originTag,
          goalBtn
        );
      }
      const childrenEl = (hasChildren && isOpen)
        ? h("div", { class: "cadmo-expansion cadmo-expanded-children" },
            ...renderProofFlow(children, { depth: depth + 1, scope })
          )
        : null;
      emitSentence(sent, childrenEl);
    }

    if (paraChildren.length > 0) {
      flushPara(true);
    } else if (appendQed) {
      out.push(h("div", { class: "cadmo-qed", "aria-hidden": "true" }, "□"));
    }
    return out;
  }

  function toggleId(id) {
    if (state.expanded.has(id)) state.expanded.delete(id);
    else state.expanded.add(id);
    renderAll();
  }

  function jumpToSectionContext(sectionId) {
    if (!sectionId) return;
    const target = document.getElementById(`${sectionId}-context`) || document.getElementById(sectionId);
    if (!target) return;
    target.scrollIntoView({ behavior: "smooth", block: "center" });
    target.classList.add("is-context-highlighted");
    window.setTimeout(() => target.classList.remove("is-context-highlighted"), 1600);
  }

  function renderInspectorRichBody(ins, opts = {}) {
    const { compact = false } = opts;
    const kind = ins.kind || {};
    let kicker = "Symbol";
    const body = [];
    if (kind.interfaceTable) {
      kicker = "Interface";
      const it = kind.interfaceTable;
      if (it.domainLatex) body.push(h("p", {}, "Domain: ", renderMathSpan(it.domainLatex, false, null)));
      const rows = (it.ports || []).map((p) =>
        h("tr", {},
          h("td", {}, p.port),
          h("td", {}, renderMathSpan(p.queryLatex, false, null)),
          h("td", {}, renderMathSpan(p.replyLatex, false, null))
        )
      );
      if (rows.length > 0) {
        body.push(h("table", { class: "cadmo-inspector-table" },
          h("thead", {}, h("tr", {}, h("th", {}, "Port"), h("th", {}, "Query"), h("th", {}, "Reply"))),
          h("tbody", {}, ...rows)
        ));
      }
      if (it.budgetNote) body.push(h("p", {}, renderMixedText(it.budgetNote, null)));
    } else if (kind.dslPseudocode) {
      kicker = "System / Converter";
      const dp = kind.dslPseudocode;
      if (dp.header) body.push(h("p", {}, h("strong", {}, dp.header)));
      body.push(h("pre", { class: "cadmo-pseudocode" }, dp.body || dp.fullSource || ""));
    } else if (kind.ccDiagram) {
      kicker = "CC Assembly";
      const d = kind.ccDiagram;
      if (d.summaryLatex) body.push(renderMathSpan(d.summaryLatex, true, null));
      const cleanSvgOrHtml = stripEmbeddedStyles(d.svgOrHtml || "").trim();
      if (cleanSvgOrHtml) {
        const diagWrap = h("div", { class: "cadmo-diagram cadmo-inspector-diagram" });
        const diagBody = h("div", { class: "cadmo-diagram-body" });
        diagBody.innerHTML = cleanSvgOrHtml;
        diagWrap.appendChild(diagBody);
        body.push(diagWrap);
      }
    } else if (kind.mathDefinition) {
      kicker = "Definition";
      const md = kind.mathDefinition;
      if (md.proseSummary) body.push(h("p", {}, renderMixedText(md.proseSummary, null)));
      if (md.equationLatex) body.push(renderMathSpan(md.equationLatex, true, null));
    } else if (kind.witnessCard) {
      kicker = "Witness";
      const wc = kind.witnessCard;
      if (wc.title) body.push(h("p", {}, h("strong", {}, renderMixedText(wc.title, null))));
      const rows = (wc.rows || []).map(([k, v]) =>
        h("tr", {}, h("th", {}, k), h("td", {}, renderMixedText(v, null)))
      );
      body.push(h("table", { class: "cadmo-inspector-table" }, h("tbody", {}, ...rows)));
    } else if (kind.parameter) {
      kicker = "Parameter";
      const rd = typeof kind.parameter === "string" ? kind.parameter : (kind.parameter.roleDescription || "");
      if (rd) body.push(h("p", {}, renderMixedText(rd, null)));
    } else if (kind.localShorthand) {
      kicker = "Local shorthand";
      const ls = kind.localShorthand;
      if (ls.roleDescription) body.push(h("p", {}, renderMixedText(ls.roleDescription, null)));
      if (ls.equationLatex) body.push(renderMathSpan(ls.equationLatex, !compact, null));
    }

    if (ins.sectionAssumptions && ins.sectionAssumptions.length > 0) {
      const assumptionParts = [];
      ins.sectionAssumptions.forEach((a, idx) => {
        if (idx > 0) assumptionParts.push("; ");
        assumptionParts.push(renderInlines(a, null));
      });
      body.push(h("p", {}, h("strong", {}, "Assumed in section: "), ...assumptionParts));
    }

    if (ins.docString) {
      body.push(h("p", { class: "cadmo-sidenote-doc" }, renderMixedText(ins.docString, null)));
    }

    if (ins.clauses && ins.clauses.length > 0) {
      body.push(
        h("ul", { class: "cadmo-sidenote-clauses" },
          ...ins.clauses.map((c) => h("li", {}, renderMathSpan(c, false, null)))
        )
      );
    }

    const finalKicker = ins.roleBadge || kicker;
    const sectionNum = ins.sectionId ? (secNumById.get(ins.sectionId) || null) : null;
    return { kicker: finalKicker, body, sectionNum };
  }

  function ensurePopoverEl() {
    if (popoverEl && popoverEl.isConnected) return popoverEl;
    popoverEl = h("div", {
      class: "cadmo-popover",
      hidden: true,
      role: "dialog",
      "aria-live": "polite"
    });
    popoverEl.addEventListener("mouseenter", () => {
      if (hidePopoverTimer) {
        window.clearTimeout(hidePopoverTimer);
        hidePopoverTimer = null;
      }
    });
    popoverEl.addEventListener("focusin", () => {
      if (hidePopoverTimer) {
        window.clearTimeout(hidePopoverTimer);
        hidePopoverTimer = null;
      }
    });
    popoverEl.addEventListener("mouseleave", () => scheduleHidePopover(160));
    popoverEl.addEventListener("focusout", (ev) => {
      if (activePopover.anchor && activePopover.anchor.contains(ev.relatedTarget)) return;
      if (popoverEl.contains(ev.relatedTarget)) return;
      scheduleHidePopover(160);
    });
    document.body.appendChild(popoverEl);
    return popoverEl;
  }

  function hidePopover(immediate = false) {
    if (hidePopoverTimer) {
      window.clearTimeout(hidePopoverTimer);
      hidePopoverTimer = null;
    }
    if (!immediate) return;
    if (popoverEl) popoverEl.hidden = true;
    activePopover = { anchor: null, candidates: [], index: 0 };
  }

  function scheduleHidePopover(delayMs = 160) {
    if (hidePopoverTimer) window.clearTimeout(hidePopoverTimer);
    hidePopoverTimer = window.setTimeout(() => {
      hidePopoverTimer = null;
      if (!popoverEl) return;
      if (popoverEl.matches(":hover") || (popoverEl.contains(document.activeElement))) return;
      if (activePopover.anchor && (activePopover.anchor.matches(":hover") || activePopover.anchor === document.activeElement)) return;
      hidePopover(true);
    }, delayMs);
  }

  function positionPopover(anchorEl) {
    if (!popoverEl || !anchorEl || !anchorEl.isConnected) return;
    const rect = anchorEl.getBoundingClientRect();
    if (rect.bottom < 0 || rect.top > window.innerHeight) {
      hidePopover(true);
      return;
    }
    popoverEl.hidden = false;
    const popRect = popoverEl.getBoundingClientRect();
    const pad = 12;
    let left = Math.min(Math.max(pad, rect.left), Math.max(pad, window.innerWidth - popRect.width - pad));
    let top = rect.bottom + 8;
    if (top + popRect.height > window.innerHeight - pad && rect.top - popRect.height - 8 >= pad) {
      top = rect.top - popRect.height - 8;
    } else if (top + popRect.height > window.innerHeight - pad) {
      top = Math.max(pad, window.innerHeight - popRect.height - pad);
    }
    popoverEl.style.left = `${Math.round(left)}px`;
    popoverEl.style.top = `${Math.round(top)}px`;
  }

  function renderPopoverContent() {
    const pop = ensurePopoverEl();
    const { anchor, candidates, index } = activePopover;
    const ins = candidates[index];
    if (!anchor || !ins) {
      hidePopover(true);
      return;
    }
    const { kicker, body, sectionNum } = renderInspectorRichBody(ins, { compact: true });
    const candNav = candidates.length > 1
      ? h("div", { class: "cadmo-popover-cands" },
          h("button", {
            type: "button",
            class: "cadmo-action-link",
            "aria-label": "Previous candidate",
            onClick: (ev) => {
              ev.stopPropagation();
              activePopover.index = (index + candidates.length - 1) % candidates.length;
              renderPopoverContent();
            }
          }, "‹"),
          h("span", {}, `${index + 1}/${candidates.length}`),
          h("button", {
            type: "button",
            class: "cadmo-action-link",
            "aria-label": "Next candidate",
            onClick: (ev) => {
              ev.stopPropagation();
              activePopover.index = (index + 1) % candidates.length;
              renderPopoverContent();
            }
          }, "›")
        )
      : null;

    const actions = h("div", { class: "cadmo-popover-actions" },
      ins.sectionId && (document.getElementById(`${ins.sectionId}-context`) || document.getElementById(ins.sectionId))
        ? h("button", {
            type: "button",
            class: "cadmo-action-link",
            onClick: (ev) => {
              ev.stopPropagation();
              const sid = ins.sectionId;
              hidePopover(true);
              jumpToSectionContext(sid);
            }
          }, `Jump to §${sectionNum || "?"} context`)
        : null,
      h("button", {
        type: "button",
        class: "cadmo-action-link",
        onClick: (ev) => {
          ev.stopPropagation();
          state.inspector = { type: "symbol", item: ins };
          hidePopover(true);
          renderMarginOnly();
        }
      }, "Pin in margin")
    );

    pop.innerHTML = "";
    pop.appendChild(
      h("div", { class: "cadmo-popover-head" },
        h("div", { class: "cadmo-popover-title-wrap" },
          h("h4", { class: "cadmo-popover-title" }, renderMathSpan(ins.display, false, null)),
          h("span", { class: "cadmo-role-badge" }, kicker)
        ),
        candNav
      )
    );
    pop.appendChild(h("div", { class: "cadmo-popover-body" }, ...body));
    pop.appendChild(actions);
    positionPopover(anchor);
    scheduleFitDiagrams(pop);
  }

  function showPopover(anchorEl, candidates) {
    if (!anchorEl || !Array.isArray(candidates) || candidates.length === 0) return;
    if (hidePopoverTimer) {
      window.clearTimeout(hidePopoverTimer);
      hidePopoverTimer = null;
    }
    const sameAnchor = activePopover.anchor === anchorEl;
    activePopover = {
      anchor: anchorEl,
      candidates,
      index: sameAnchor ? Math.min(activePopover.index, candidates.length - 1) : 0
    };
    renderPopoverContent();
  }

  let repositionPending = false;
  function schedulePopoverReposition() {
    if (!popoverEl || popoverEl.hidden || !activePopover.anchor || repositionPending) return;
    repositionPending = true;
    window.requestAnimationFrame(() => {
      repositionPending = false;
      if (popoverEl && !popoverEl.hidden && activePopover.anchor) {
        positionPopover(activePopover.anchor);
      }
    });
  }

  function initGlobalListeners() {
    document.addEventListener("keydown", (ev) => {
      if (ev.key === "Escape" && popoverEl && !popoverEl.hidden) {
        hidePopover(true);
      }
    });
    document.addEventListener("toggle", (ev) => {
      const t = ev && ev.target;
      if (t && t.tagName === "DETAILS" && t.open && typeof t.closest === "function" &&
          (t.classList.contains("cadmo-diagram") || t.classList.contains("ccw") || t.closest(".cadmo-diagram"))) {
        scheduleFitDiagrams(t.closest(".cadmo-diagram") || t);
      }
    }, true);
    if (typeof window !== "undefined") {
      let fitResizeTimer = null;
      window.addEventListener("scroll", schedulePopoverReposition, { passive: true });
      window.addEventListener("resize", () => {
        schedulePopoverReposition();
        if (fitResizeTimer) window.clearTimeout(fitResizeTimer);
        fitResizeTimer = window.setTimeout(() => {
          fitResizeTimer = null;
          fitDiagrams(document);
        }, 80);
      });
    }
  }

  /* ------------------------------------------------------------------------
     Tufte Sidenote Margin: completely blank by default.
     Only renders what the reader explicitly requested.
     ------------------------------------------------------------------------ */
  function renderMargin(glossaryItems) {
    const items = [];

    if (state.inspector) {
      if (state.inspector.type === "symbol") {
        const ins = state.inspector.item;
        const { kicker, body, sectionNum } = renderInspectorRichBody(ins, { compact: false });
        const jumpAction =
          ins.sectionId && (document.getElementById(`${ins.sectionId}-context`) || document.getElementById(ins.sectionId))
            ? h("div", { class: "cadmo-sidenote-actions" },
                h("button", {
                  type: "button",
                  class: "cadmo-action-link",
                  onClick: () => jumpToSectionContext(ins.sectionId)
                }, `Jump to §${sectionNum || "?"} context`)
              )
            : null;

        items.push(h("section", { class: "cadmo-sidenote" },
          h("div", { class: "cadmo-sidenote-head" },
            h("div", {},
              h("div", { class: "cadmo-sidenote-kicker" }, kicker),
              h("h3", { class: "cadmo-sidenote-title" }, renderMathSpan(ins.display, false, null))
            ),
            h("button", {
              type: "button",
              class: "cadmo-close-btn",
              "aria-label": "Dismiss note",
              onClick: () => { state.inspector = null; renderMarginOnly(); }
            }, "×")
          ),
          ...body,
          jumpAction,
          h("details", { class: "cadmo-lean-details" },
            h("summary", {}, "Lean signature"),
            h("div", { class: "cadmo-lean-code" },
              (ins.leanName ? `${ins.leanName} :\n` : "") + (ins.leanType || "")
            )
          )
        ));
      } else if (state.inspector.type === "goal") {
        const g = state.inspector.goal;
        const ctxItems = (g.context || []).map((c) =>
          h("li", {},
            c.name ? h("strong", {}, renderMixedText(c.name), ": ") : null,
            renderMixedText(c.description || "")
          )
        );
        items.push(h("section", { class: "cadmo-sidenote" },
          h("div", { class: "cadmo-sidenote-head" },
            h("div", {},
              h("div", { class: "cadmo-sidenote-kicker" }, "Proof state"),
              h("h3", { class: "cadmo-sidenote-title" }, state.inspector.label || "Goal")
            ),
            h("button", {
              type: "button",
              class: "cadmo-close-btn",
              "aria-label": "Dismiss note",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "×")
          ),
          ctxItems.length > 0
            ? h("div", {},
                h("div", { class: "cadmo-sidenote-kicker" }, "Context"),
                h("ul", { class: "cadmo-goal-ctx" }, ...ctxItems)
              )
            : null,
          h("div", { class: "cadmo-sidenote-kicker" }, "Goal"),
          h("div", { class: "cadmo-goal-target" }, renderMathSpan(g.targetLatex || "", false)),
          g.rawLeanGoal
            ? h("details", { class: "cadmo-lean-details" },
                h("summary", {}, "Raw Lean goal"),
                h("div", { class: "cadmo-lean-code" }, g.rawLeanGoal)
              )
            : null
        ));
      } else if (state.inspector.type === "axioms") {
        const e = state.inspector.entry;
        const ax = e.axioms || { axioms: [], hasSorry: false };
        items.push(h("section", { class: "cadmo-sidenote" },
          h("div", { class: "cadmo-sidenote-head" },
            h("div", {},
              h("div", { class: "cadmo-sidenote-kicker" }, "Kernel verification"),
              h("h3", { class: "cadmo-sidenote-title" }, e.title || e.declaration)
            ),
            h("button", {
              type: "button",
              class: "cadmo-close-btn",
              "aria-label": "Dismiss note",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "×")
          ),
          h("p", {}, ax.hasSorry
            ? "Warning: this declaration depends on sorryAx."
            : "Verified by the Lean kernel using standard axioms only."),
          h("div", { class: "cadmo-lean-code" },
            `${e.declaration}\n\n` +
            ((ax.axioms && ax.axioms.length > 0) ? ax.axioms.join("\n") : "(no axioms)")
          )
        ));
      }
    }

    if (state.glossaryOpen && glossaryItems.length > 0) {
      const q = (state.glossaryQuery || "").trim().toLowerCase();
      const filtered = q
        ? glossaryItems.filter((ins) =>
            (ins.display || "").toLowerCase().includes(q) ||
            (ins.key || "").toLowerCase().includes(q)
          )
        : glossaryItems;

      const grouped = new Map();
      for (const cat of ["Interfaces", "Systems & Converters", "Proof Witnesses", "Definitions", "Cited Results"]) {
        grouped.set(cat, []);
      }
      for (const ins of filtered) {
        const cat = glossaryCategory(ins);
        if (!grouped.has(cat)) grouped.set(cat, []);
        grouped.get(cat).push(ins);
      }

      const groupNodes = [];
      for (const [cat, list] of grouped.entries()) {
        if (list.length === 0) continue;
        groupNodes.push(
          h("div", { class: "cadmo-glossary-group" },
            h("h5", {}, cat),
            h("ul", { class: "cadmo-glossary-list" },
              ...list.map((ins) =>
                h("li", {},
                  h("button", {
                    type: "button",
                    class: "cadmo-glossary-item",
                    onClick: () => { state.inspector = { type: "symbol", item: ins }; renderAll(); }
                  }, renderMathSpan(ins.display, false))
                )
              )
            )
          )
        );
      }

      items.push(h("section", { class: "cadmo-sidenote" },
        h("div", { class: "cadmo-sidenote-head" },
          h("div", { class: "cadmo-sidenote-kicker" }, `Glossary (${glossaryItems.length})`),
          h("button", {
            type: "button",
            class: "cadmo-close-btn",
            "aria-label": "Close glossary",
            onClick: () => { state.glossaryOpen = false; renderAll(); }
          }, "×")
        ),
        glossaryItems.length > 6
          ? h("input", {
              type: "search",
              class: "cadmo-glossary-filter",
              placeholder: "Filter…",
              value: state.glossaryQuery,
              onInput: (ev) => {
                state.glossaryQuery = ev.target.value;
                renderAll();
              }
            })
          : null,
        ...groupNodes
      ));
    }

    return h("aside", { class: "cadmo-margin", "aria-label": "Margin notes" }, ...items);
  }

  function renderEntry(entry, idx, suppressAmbient = false, scope = null) {
    const ax = entry.axioms || { axioms: [], hasSorry: false };
    const proofNodes = projectNodes(entry.proof || []);
    return h("article", { class: "cadmo-entry", id: `decl-${entry.declaration}` },
      h("header", { class: "cadmo-entry-head" },
        h("h2", { class: "cadmo-entry-heading" },
          h("span", { class: "cadmo-entry-kind" }, `${entry.header || "Theorem"} ${idx + 1}.`),
          entry.title ? h("span", { class: "cadmo-entry-title" }, " (", renderMixedText(entry.title, scope), ")") : null
        ),
        h("button", {
          type: "button",
          class: "cadmo-axiom-link" + (ax.hasSorry ? " has-sorry" : ""),
          onClick: () => { state.inspector = { type: "axioms", entry }; renderMarginOnly(); }
        }, ax.hasSorry ? "sorry" : "axioms")
      ),
      (!suppressAmbient && entry.ambient)
        ? h("p", { class: "cadmo-ambient" },
            h("span", { class: "cadmo-ambient-label" }, "Setting."),
            renderInlines(entry.ambient.summary || [], scope)
          )
        : null,
      h("div", { class: "cadmo-statement" },
        ...(entry.statement || []).map((para) => h("p", {}, renderInlines(para, scope)))
      ),
      renderCollapsibleDiagram(entry.diagramHtml, "cadmo-entry-diagram", "System figure", false),
      proofNodes.length > 0
        ? h("section", { class: "cadmo-proof" },
            ...renderProofFlow(entry.proof || [], { leadIn: "Proof.", appendQed: true, depth: 0, scope })
          )
        : null
    );
  }

  function renderMarginOnly() {
    if (!marginElRef || !marginElRef.isConnected) {
      renderAll();
      return;
    }
    const glossaryItems = (doc.inspectors || []).filter(isGlossaryWorthy);
    const nextMargin = renderMargin(glossaryItems);
    marginElRef.replaceWith(nextMargin);
    marginElRef = nextMargin;
    syncActiveAriaPressed();
    scheduleFitDiagrams(marginElRef);
  }

  function renderAll() {
    document.documentElement.dataset.mode = state.mode;
    document.documentElement.dataset.theme = state.theme;
    hoverInteractiveNodes.clear();
    hidePopover(true);

    const glossaryItems = (doc.inspectors || []).filter(isGlossaryWorthy);
    const hasContentsLink = !!document.querySelector('link[rel="contents"], a[data-cadmo-contents]');

    const runningBar = h("header", { class: "cadmo-running-bar" },
      h("div", { class: "cadmo-running-head" },
        hasContentsLink ? null : formatProseDashes(doc.title || "Constructive Cryptography")
      ),
      h("nav", { class: "cadmo-controls", "aria-label": "Reading options" },
        h("button", {
          type: "button",
          class: "cadmo-text-btn",
          "aria-pressed": state.mode === "paper" ? "true" : "false",
          onClick: () => { state.mode = "paper"; renderAll(); }
        }, "Paper"),
        h("span", { class: "cadmo-sep" }, "·"),
        h("button", {
          type: "button",
          class: "cadmo-text-btn",
          "aria-pressed": state.mode === "auditor" ? "true" : "false",
          onClick: () => { state.mode = "auditor"; renderAll(); }
        }, "Auditor"),
        h("span", { class: "cadmo-sep" }, "·"),
        h("button", {
          type: "button",
          class: "cadmo-text-btn",
          onClick: () => {
            const allIds = [];
            for (const e of doc.entries || []) collectAllExpandableIds(e.proof || [], allIds);
            if (state.expanded.size > 0) state.expanded.clear();
            else allIds.forEach((id) => state.expanded.add(id));
            renderAll();
          }
        }, state.expanded.size > 0 ? "Collapse proofs" : "Expand proofs"),
        glossaryItems.length > 0 ? h("span", { class: "cadmo-sep" }, "·") : null,
        glossaryItems.length > 0
          ? h("button", {
              type: "button",
              class: "cadmo-text-btn",
              "aria-pressed": state.glossaryOpen ? "true" : "false",
              onClick: () => { state.glossaryOpen = !state.glossaryOpen; renderAll(); }
            }, `Glossary (${glossaryItems.length})`)
          : null,
        h("span", { class: "cadmo-sep" }, "·"),
        h("button", {
          type: "button",
          class: "cadmo-text-btn",
          onClick: () => {
            state.theme = state.theme === "dark" ? "light" : "dark";
            renderAll();
          }
        }, state.theme === "dark" ? "Paper" : "Dark")
      )
    );

    const header = h("header", { class: "cadmo-doc-header" },
      h("h1", { class: "cadmo-doc-title" }, formatProseDashes(doc.title || "Untitled Document")),
      doc.subtitle ? h("p", { class: "cadmo-doc-subtitle" }, renderMixedText(doc.subtitle)) : null
    );

    const entries = doc.entries || [];
    const sectionsWithSetting = new Set();
    let scanSecIdx = 0;
    for (const e of entries) {
      if (e && e.sectionTitle) scanSecIdx += 1;
      if (
        scanSecIdx > 0 &&
        Array.isArray(e && e.sectionPreludes) &&
        e.sectionPreludes.some((p) => p && p.kind === "setting")
      ) {
        sectionsWithSetting.add(scanSecIdx);
      }
    }

    const bodyNodes = [];
    let sectionNum = 0;
    let activeSecId = null;
    entries.forEach((entry, idx) => {
      if (entry.sectionTitle) {
        sectionNum += 1;
        const sc = entry.sectionContext || null;
        const secNumShown = (sc && sc.sectionNumber) || sectionNum;
        const secId = (sc && sc.sectionId) || entry.sectionId || `sec-${secNumShown}`;
        activeSecId = secId;
        const secScope = buildScope(
          sc ? sc.inspectors : [],
          secId,
          Array.from(sectionRefKeys.get(secId) || []),
          true
        );
        const hasSettingPrelude = sectionsWithSetting.has(sectionNum);
        const scParas = (!hasSettingPrelude && sc && Array.isArray(sc.paragraphs) && sc.paragraphs.length > 0)
          ? h("div", { class: "cadmo-section-context", id: `${secId}-context` },
              ...sc.paragraphs.map((p, pIdx) =>
                h("p", {},
                  pIdx === 0 ? h("span", { class: "cadmo-section-context-label" }, "Section context. ") : null,
                  renderInlines(p, secScope)
                )
              )
            )
          : null;
        const secTitleStr = String(entry.sectionTitle);
        const hasExplicitSecPrefix = /^\s*(?:Section|§|Chapter|Part)\s*\d/i.test(secTitleStr);
        bodyNodes.push(
          h("div", { class: "cadmo-section-head", id: secId },
            h("h2", { class: "cadmo-section-title" },
              hasExplicitSecPrefix ? null : h("span", { class: "cadmo-section-num" }, `${secNumShown}.`),
              hasExplicitSecPrefix ? null : " ",
              renderMixedText(secTitleStr, secScope)
            ),
            entry.sectionIntro ? h("p", { class: "cadmo-section-intro" }, renderMixedText(entry.sectionIntro, secScope)) : null,
            scParas
          )
        );
      }
      const entrySecId = entry.sectionId || (entry.sectionContext && entry.sectionContext.sectionId) || activeSecId;
      if (Array.isArray(entry.sectionPreludes) && entry.sectionPreludes.length > 0) {
        const preludeKeys = entry.sectionPreludes.map((p) => p && p.declKey).filter(Boolean);
        const preludeScope = buildScope(
          entry.localInspectors || [],
          entrySecId,
          [...(entry.referencedKeys || []), ...preludeKeys],
          true
        );
        const preludesEl = renderSectionPreludes(entry, preludeScope);
        if (preludesEl) bodyNodes.push(preludesEl);
      }
      const entryScope = buildScope(
        entry.localInspectors || [],
        entrySecId,
        entry.referencedKeys || [],
        false
      );
      const isVacuousAmbient = entry.ambient && Array.isArray(entry.ambient.summary) &&
        entry.ambient.summary.length === 1 &&
        String((entry.ambient.summary[0]?.text?.value ?? entry.ambient.summary[0]?.text) || "")
          .startsWith("We work in the Constructive Cryptography framework");
      bodyNodes.push(renderEntry(entry, idx, !!isVacuousAmbient, entryScope));
    });

    marginElRef = renderMargin(glossaryItems);
    const shell = h("div", { class: "cadmo-shell" },
      h("main", { class: "cadmo-main" },
        header,
        ...bodyNodes
      ),
      marginElRef
    );

    rootEl.innerHTML = "";
    rootEl.appendChild(runningBar);
    rootEl.appendChild(shell);
    ensurePopoverEl();
    scheduleFitDiagrams(rootEl);
  }

  if (typeof globalThis !== "undefined") {
    globalThis.__cadmoHelpers = {
      SYMBOL_MAP,
      stripEmbeddedStyles,
      sanitizeDocDiagrams,
      fitDiagrams,
      extractFontPrefixFromLatex,
      normalizeUnicodeMath,
      normalizeMathToken,
      stripFontPrefix,
      isNonHoverableToken,
      isBlockedHoverNode,
      hasBlockedHoverAncestor,
      extractFontPrefixFromDomNode,
      extractFontPrefixFromDomSlice,
      buildTokenScope,
      resolveTokenCandidates,
      renderMathNodes,
      formatProseDashes,
      renderMixedText,
      annotateOfflineMathContainer,
      annotateKatexBase,
      annotateKatexMath,
      annotateMathReferences,
      getTrustLevel,
      projectNodes,
      renderPseudocodeLines,
      renderPseudocodeBox,
      renderPreludeBlock,
      renderSectionPreludes,
      renderInline,
      renderProofFlow,
      renderInspectorRichBody,
      renderEntry,
      renderAll: typeof renderAll === "function" ? renderAll : null
    };
  }

  if (typeof document === "undefined") return;
  const dataEl = document.getElementById("cadmo-document-data");
  const rootEl = document.getElementById("cadmo-root");
  if (!dataEl || !rootEl) return;

  try {
    doc = JSON.parse(dataEl.textContent || "{}");
  } catch (err) {
    rootEl.textContent = "Failed to parse informalization document JSON: " + err;
    return;
  }
  sanitizeDocDiagrams(doc);
  state.mode = doc.defaultMode === "auditor" ? "auditor" : "paper";
  initDocumentIndexes(doc);
  initGlobalListeners();
  renderAll();
})();
