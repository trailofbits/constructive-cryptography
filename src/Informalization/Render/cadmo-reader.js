/* ==========================================================================
   CADMO Interactive Proof Reader Controller
   Print-authentic monograph reader: calm whitespace, on-demand sidenotes,
   zero diagram clutter in the reading flow, real 2D offline math.
   ========================================================================== */
(() => {
  const dataEl = document.getElementById("cadmo-document-data");
  const rootEl = document.getElementById("cadmo-root");
  if (!dataEl || !rootEl) return;

  let doc;
  try {
    doc = JSON.parse(dataEl.textContent || "{}");
  } catch (err) {
    rootEl.textContent = "Failed to parse informalization document JSON: " + err;
    return;
  }

  const state = {
    mode: doc.defaultMode === "auditor" ? "auditor" : "paper",
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
  for (const ins of doc.inspectors || []) {
    inspectorByKey.set(ins.key, ins);
  }
  {
    let sNum = 0;
    let curSecId = null;
    for (const entry of doc.entries || []) {
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
    if (k.interfaceTable) return "Interfaces";
    if (k.dslPseudocode || k.ccDiagram) return "Systems & Converters";
    if (k.witnessCard) return "Proof Witnesses";
    return "Definitions";
  }

  /* ------------------------------------------------------------------------
     Real 2D offline HTML math renderer (no external CDN required; upgrades
     automatically to KaTeX if loaded).
     ------------------------------------------------------------------------ */
  function readBalanced(str, pos) {
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
    chi: "χ", psi: "ψ", omega: "ω", ell: "ℓ", star: "★",
    varnothing: "∅", emptyset: "∅", infty: "∞",
    parallel: "∥", otimes: "⊗", oplus: "⊕", equiv: "≡", simeq: "≃", approx: "≈",
    le: "≤", ge: "≥", ne: "≠", neq: "≠", implies: "⇒", iff: "⇔",
    in: "∈", notin: "∉", subseteq: "⊆", times: "×", cdot: "·", circ: "∘",
    to: "→", mapsto: "↦", forall: "∀", exists: "∃", land: "∧", wedge: "∧",
    lor: "∨", vee: "∨", neg: "¬", sum: "∑", prod: "∏", pm: "±",
    mid: "∣", preceq: "⪯", succeq: "⪰", top: "⊤", bot: "⊥", ldots: "…", dots: "…",
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
          else frag.appendChild(document.createTextNode(esc));
          i += 2;
          continue;
        }
        const cmd = tex.slice(i + 1, j);
        i = j;
        if (cmd === "left" || cmd === "right") continue;
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
        if (cmd === "xrightarrow") {
          const [lbl, next] = readBalanced(tex, i);
          frag.appendChild(document.createTextNode(" —["));
          frag.appendChild(renderMathNodes(lbl));
          frag.appendChild(document.createTextNode("]→ "));
          i = next;
          continue;
        }
        if (cmd === "mathbb") {
          const [arg, next] = readBalanced(tex, i);
          const bb = { R: "ℝ", N: "ℕ", Z: "ℤ", Q: "ℚ", C: "ℂ" }[arg] || arg;
          const span = document.createElement("span");
          span.className = "cadmo-msym";
          span.textContent = bb;
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (cmd === "mathcal") {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          span.className = "cadmo-cal";
          span.textContent = arg;
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (
          cmd === "mathrm" || cmd === "mathsf" || cmd === "operatorname" ||
          cmd === "text" || cmd === "texttt" || cmd === "mathbf" ||
          cmd === "boldsymbol" || cmd === "mathrel" || cmd === "mathit"
        ) {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          if (cmd === "text" || cmd === "texttt") {
            span.className = "cadmo-mtext";
            span.textContent = arg.replace(/\\_/g, "_");
          } else {
            span.className = "cadmo-op";
            if (cmd === "mathbf" || cmd === "boldsymbol") span.style.fontWeight = "600";
            if (cmd === "mathrm" || cmd === "mathsf" || cmd === "operatorname" || cmd === "mathit") {
              span.textContent = arg.replace(/\\_/g, "_");
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
          span.className = "cadmo-msym";
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

  function normalizeUnicodeMath(str) {
    return Array.from(str || "").map((ch) => {
      if (UNICODE_SCRIPT_MAP[ch] !== undefined) return UNICODE_SCRIPT_MAP[ch];
      const cp = ch.codePointAt(0);
      if (cp >= 0x1d400 && cp <= 0x1d419) return String.fromCharCode(65 + (cp - 0x1d400));
      if (cp >= 0x1d41a && cp <= 0x1d433) return String.fromCharCode(97 + (cp - 0x1d41a));
      if (cp >= 0x1d434 && cp <= 0x1d44d) return String.fromCharCode(65 + (cp - 0x1d434));
      if (cp >= 0x1d44e && cp <= 0x1d467) return String.fromCharCode(97 + (cp - 0x1d44e));
      if (cp >= 0x1d5d4 && cp <= 0x1d5ed) return String.fromCharCode(65 + (cp - 0x1d5d4));
      if (cp >= 0x1d5ee && cp <= 0x1d607) return String.fromCharCode(97 + (cp - 0x1d5ee));
      return ch;
    }).join("");
  }

  function normalizeMathToken(raw) {
    if (!raw) return "";
    let s = normalizeUnicodeMath(String(raw)).replace(/[\u200b\u2009]/g, "");
    let prev;
    do {
      prev = s;
      s = s
        .replace(/\\(?:mathrm|mathit|mathsf|mathbf|mathcal|operatorname|text|texttt|boldsymbol)\{([^{}]*)\}/g, "$1")
        .replace(/\\mathbb\{([^{}]*)\}/g, (_, arg) => ({ R: "ℝ", N: "ℕ", Z: "ℤ", Q: "ℚ", C: "ℂ" }[arg] || arg));
    } while (s !== prev);
    s = s
      .replace(/\\(?:left|right|middle)\b/g, "")
      .replace(/\\[!,;: ]/g, "")
      .replace(/\\_/g, "_")
      .replace(/\\([A-Za-z]+)/g, (_, cmd) => (SYMBOL_MAP[cmd] !== undefined ? SYMBOL_MAP[cmd] : cmd))
      .replace(/[{}_\s]/g, "");
    return s;
  }

  const NON_TOKEN_RE = /^[0-9()[\]{},.;:=<>+\-*/·⋅∣|!?~'"\\]+$/;
  const NON_ATOM_REL_TEXT = /^[\u200b\u2009()[\]{},.;:=<>+\-*/·⋅∣|\s]+$/;
  const elementCandidates = new WeakMap();
  const hoverInteractiveNodes = new Set();

  function buildScope(localInspectors, sectionId, referencedKeys, includeSectionContextDefs = false) {
    const tokenMap = new Map();
    const tierMap = new Map(); // norm -> tier (1=local, 2=section, 3=global)

    function addCandidate(ins, tier) {
      if (!ins || !ins.display) return;
      const norm = normalizeMathToken(ins.display);
      if (!norm || norm.length > 48 || NON_TOKEN_RE.test(norm)) return;
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
    const secCtx = sectionId ? sectionContextById.get(sectionId) : null;
    if (secCtx) {
      for (const ins of secCtx.inspectors || []) addCandidate(ins, 2);
    }

    const refSet = new Set(referencedKeys || []);
    const useRefFilter = refSet.size > 0 && !includeSectionContextDefs;
    for (const ins of doc.inspectors || []) {
      if (ins.sectionId && sectionId && ins.sectionId !== sectionId) continue;
      const k = ins.key || "";
      if (k.startsWith("sec:") || k.startsWith("param:") || k.startsWith("shorthand:") || k.startsWith("secparam:")) continue;
      if (useRefFilter && !refSet.has(k)) continue;
      addCandidate(ins, 3);
    }
    // Fallback: if Section Context mentions definitions/predicates not explicitly in sectionRefKeys
    if (includeSectionContextDefs || refSet.size === 0) {
      for (const ins of doc.inspectors || []) {
        if (ins.sectionId && sectionId && ins.sectionId !== sectionId) continue;
        const k = ins.key || "";
        if (k.startsWith("sec:") || k.startsWith("param:") || k.startsWith("shorthand:") || k.startsWith("secparam:")) continue;
        addCandidate(ins, 3);
      }
    }

    return { tokenMap, sectionId: sectionId || null };
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

  function attachInteractiveToken(el, candidates, displayHint) {
    elementCandidates.set(el, candidates);
    hoverInteractiveNodes.add(el);
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

  function isRefTargetContainer(node) {
    return node && node.nodeType === 1 &&
      !node.classList.contains("cadmo-ref") &&
      !node.classList.contains("cadmo-sym") &&
      !node.classList.contains("cadmo-mtext");
  }

  function wrapSiblingSlice(parent, sliceNodes, candidates) {
    if (!sliceNodes || sliceNodes.length === 0) return;
    const span = document.createElement("span");
    span.className = "cadmo-ref";
    const labelText = sliceNodes.map((n) => n.textContent || "").join("");
    parent.insertBefore(span, sliceNodes[0]);
    for (const n of sliceNodes) span.appendChild(n);
    attachInteractiveToken(span, candidates, labelText);
  }

  function annotateOfflineMathContainer(container, scope) {
    if (!container || !scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    const children = Array.from(container.childNodes);
    let i = 0;
    while (i < children.length) {
      const node = children[i];
      if (node.nodeType !== 1 || !isRefTargetContainer(node)) {
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
        // Stop span at text nodes (except trailing none) or .cadmo-mtext
        let validSlice = true;
        for (let k = i; k <= end; k++) {
          const cur = children[k];
          if (cur.nodeType !== 1 || !isRefTargetContainer(cur)) {
            validSlice = false;
            break;
          }
        }
        if (!validSlice) continue;

        // Do not peel base alone when immediately followed by SUB (e.g. R_MAC or x_1)
        if (
          end + 1 < children.length &&
          children[end + 1].nodeType === 1 &&
          children[end + 1].tagName === "SUB" &&
          isSubAtomEl(children[end])
        ) {
          continue;
        }

        const slice = children.slice(i, end + 1);
        const rawText = slice.map((n) => n.textContent || "").join("");
        const norm = normalizeMathToken(rawText);
        if (norm && !NON_TOKEN_RE.test(norm)) {
          const candidates = scope.tokenMap.get(norm);
          if (candidates && candidates.length > 0) {
            wrapSiblingSlice(container, slice, candidates);
            i = end + 1;
            matched = true;
            break;
          }
        }
      }

      if (matched) continue;

      if (isBareVarRun) {
        // Multi-letter identifier like un-escaped `uniform`: skip whole run instead of slicing single letters
        if (varRunEnd + 1 < children.length && children[varRunEnd + 1].tagName === "SUB") {
          annotateOfflineMathContainer(children[varRunEnd + 1], scope);
          i = varRunEnd + 2;
        } else {
          i = varRunEnd + 1;
        }
        continue;
      }

      annotateOfflineMathContainer(node, scope);
      i += 1;
    }
  }

  function annotateKatexBase(baseEl, scope) {
    const items = Array.from(baseEl.children).filter(
      (el) => el.classList && !el.classList.contains("cadmo-ref") && !el.classList.contains("mspace")
    );
    let i = 0;
    while (i < items.length) {
      let matched = false;
      const maxEnd = Math.min(items.length - 1, i + 6);
      for (let end = maxEnd; end >= i; end--) {
        const slice = items.slice(i, end + 1);
        if (slice.some((el) => el.classList.contains("mtext"))) continue;
        const norm = normalizeMathToken(slice.map((el) => el.textContent || "").join(""));
        if (norm && !NON_TOKEN_RE.test(norm)) {
          const candidates = scope.tokenMap.get(norm);
          if (candidates && candidates.length > 0) {
            wrapSiblingSlice(baseEl, slice, candidates);
            i = end + 1;
            matched = true;
            break;
          }
        }
      }
      if (!matched) {
        const subContainers = items[i].querySelectorAll(".msupsub, .mfrac");
        subContainers.forEach((sc) => annotateKatexMath(sc, scope));
        i += 1;
      }
    }
  }

  function annotateKatexMath(root, scope) {
    if (!root || !scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    const bases = root.querySelectorAll(".base");
    if (bases.length > 0) {
      bases.forEach((b) => annotateKatexBase(b, scope));
    } else {
      annotateKatexBase(root, scope);
    }
  }

  function annotateMathReferences(mathEl, scope) {
    if (!mathEl || !scope || !scope.tokenMap || scope.tokenMap.size === 0) return;
    const katexHtml = mathEl.querySelector(".katex-html");
    if (katexHtml) {
      annotateKatexMath(katexHtml, scope);
    } else {
      annotateOfflineMathContainer(mathEl, scope);
    }
  }

  function renderMathSpan(tex, displayMode = false, scope = null) {
    const el = document.createElement(displayMode ? "div" : "span");
    el.className = displayMode ? "cadmo-display-math" : "cadmo-math";
    el.dataset.latex = tex || "";
    if (window.katex && typeof window.katex.render === "function") {
      try {
        window.katex.render(tex || "", el, { displayMode, throwOnError: false });
        annotateMathReferences(el, scope);
        return el;
      } catch (_) {
        /* fallback below */
      }
    }
    el.appendChild(renderMathNodes(tex || ""));
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

  function renderMixedText(str, scope = null) {
    const frag = document.createDocumentFragment();
    if (!str) return frag;
    const re = /\\\(([\s\S]*?)\\\)/g;
    let last = 0;
    let m;
    while ((m = re.exec(str)) !== null) {
      if (m.index > last) frag.appendChild(document.createTextNode(str.slice(last, m.index)));
      frag.appendChild(renderMathSpan(m[1], false, scope));
      last = re.lastIndex;
    }
    if (last < str.length) frag.appendChild(document.createTextNode(str.slice(last)));
    return frag;
  }

  function renderInline(inl, scope = null) {
    if (!inl || typeof inl !== "object") return document.createTextNode("");
    if (inl.text !== undefined) {
      const val = typeof inl.text === "string" ? inl.text : inl.text.value;
      return renderMixedText(val || "", scope);
    }
    if (inl.emph !== undefined) {
      const val = typeof inl.emph === "string" ? inl.emph : inl.emph.value;
      return h("em", {}, val || "");
    }
    if (inl.inlineMath !== undefined) {
      const tex = typeof inl.inlineMath === "string" ? inl.inlineMath : inl.inlineMath.latex;
      return renderMathSpan(tex || "", false, scope);
    }
    if (inl.displayMath !== undefined) {
      const obj = inl.displayMath;
      const tex = typeof obj === "string" ? obj : obj.latex;
      const punct = typeof obj === "object" && obj.punct ? obj.punct : "";
      return renderMathSpan((tex || "") + (punct ? "\\," + punct : ""), true, scope);
    }
    if (inl.symbol !== undefined) {
      const sym = inl.symbol;
      const ins = inspectorByKey.get(sym.key);
      const isSelected = state.inspector && state.inspector.type === "symbol" &&
        state.inspector.item.key === sym.key;
      const btn = h("button", {
        type: "button",
        class: sym.isMath ? "cadmo-sym" : "cadmo-sym cadmo-sym-prose",
        "aria-pressed": isSelected ? "true" : "false"
      }, sym.isMath ? renderMathSpan(sym.display, false, null) : sym.display);
      if (ins) {
        attachInteractiveToken(btn, [ins], sym.display);
      } else {
        btn.addEventListener("click", () => {
          state.inspector = null;
          renderMarginOnly();
        });
      }
      return btn;
    }
    if (inl.citation !== undefined) {
      const c = inl.citation;
      return h("span", { title: c.detail || "" }, `[${c.label}]`);
    }
    return document.createTextNode("");
  }

  function renderInlines(arr, scope = null) {
    const frag = document.createDocumentFragment();
    for (const item of arr || []) frag.appendChild(renderInline(item, scope));
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
        usedLeadIn = true;
      }
    }

    function emitSentence(sentEl, childrenEl = null) {
      if (depth > 0) {
        flushPara(false);
        const kids = [];
        if (leadIn && !usedLeadIn) {
          kids.push(h("span", { class: "cadmo-proof-lead" }, leadIn));
          usedLeadIn = true;
        }
        kids.push(sentEl);
        out.push(h("div", { class: "cadmo-expanded-step" }, ...kids));
        if (childrenEl) out.push(childrenEl);
      } else {
        ensureLeadIn();
        paraChildren.push(sentEl);
        if (childrenEl) {
          flushPara(false);
          out.push(childrenEl);
        }
      }
    }

    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      if (!node || node.kind === "figure") continue;

      if (node.kind === "flowNote") {
        flushPara(false);
        const p = h("p", { class: "cadmo-flow-note" }, renderMixedText(node.text || "", scope));
        out.push(p);
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
                ch.length > 0
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
          if (ch.length > 0 && isOpen) {
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
      const children = paperVisibleChildren(node.children || []);
      const hasChildren = children.length > 0;
      const isOpen = state.expanded.has(node.id);
      const sent = h("span", { class: "cadmo-sent" + (node.isWrapper ? " is-wrapper" : "") },
        renderInlines(node.content || [], scope),
        hasChildren
          ? h("button", {
              type: "button",
              class: "cadmo-inline-toggle",
              "aria-expanded": isOpen ? "true" : "false",
              title: isOpen ? "Collapse subproof" : "Expand subproof",
              onClick: () => toggleId(node.id)
            }, isOpen ? "⊖" : "⊕")
          : null,
        node.isWrapper ? h("span", { class: "cadmo-wrapper-tag" }, "[wrapper]") : null,
        node.originDecl ? h("span", { class: "cadmo-origin-tag" }, node.originDecl) : null,
        renderGoalButton(node.goal, node.originDecl || "Proof step")
      );
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
        h("tr", {}, h("th", {}, k), h("td", {}, renderMathSpan(v, false, null)))
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

  document.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape" && popoverEl && !popoverEl.hidden) {
      hidePopover(true);
    }
  });
  window.addEventListener("scroll", schedulePopoverReposition, { passive: true });
  window.addEventListener("resize", schedulePopoverReposition);

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
      for (const cat of ["Interfaces", "Systems & Converters", "Proof Witnesses", "Definitions"]) {
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
          entry.title ? h("span", { class: "cadmo-entry-title" }, ` (${entry.title})`) : null
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
        hasContentsLink ? null : (doc.title || "Constructive Cryptography")
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
      h("h1", { class: "cadmo-doc-title" }, doc.title || "Untitled Document"),
      doc.subtitle ? h("p", { class: "cadmo-doc-subtitle" }, doc.subtitle) : null
    );

    const entries = doc.entries || [];
    // Hoist shared chapter-level ambient setting ONCE so it never repeats 41 times
    const firstAmbient = entries.find((e) => e.ambient && e.ambient.summary)?.ambient || null;
    const chapterScope = buildScope([], null, [], true);
    const bodyNodes = [];
    if (firstAmbient) {
      bodyNodes.push(
        h("p", { class: "cadmo-chapter-setting" },
          h("span", { class: "cadmo-ambient-label" }, "Standing conventions. "),
          renderInlines(firstAmbient.summary || [], chapterScope)
        )
      );
    }
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
        const scParas = sc && Array.isArray(sc.paragraphs) && sc.paragraphs.length > 0
          ? h("div", { class: "cadmo-section-context", id: `${secId}-context` },
              ...sc.paragraphs.map((p, pIdx) =>
                h("p", {},
                  pIdx === 0 ? h("span", { class: "cadmo-section-context-label" }, "Section context. ") : null,
                  renderInlines(p, secScope)
                )
              )
            )
          : null;
        bodyNodes.push(
          h("div", { class: "cadmo-section-head", id: secId },
            h("h2", { class: "cadmo-section-title" },
              h("span", { class: "cadmo-section-num" }, `${secNumShown}.`),
              entry.sectionTitle
            ),
            entry.sectionIntro ? h("p", { class: "cadmo-section-intro" }, entry.sectionIntro) : null,
            scParas
          )
        );
      }
      const entrySecId = entry.sectionId || (entry.sectionContext && entry.sectionContext.sectionId) || activeSecId;
      const entryScope = buildScope(
        entry.localInspectors || [],
        entrySecId,
        entry.referencedKeys || [],
        false
      );
      bodyNodes.push(renderEntry(entry, idx, !!firstAmbient, entryScope));
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
  }

  renderAll();
})();
