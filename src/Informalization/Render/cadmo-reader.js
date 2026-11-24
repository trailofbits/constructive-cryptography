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

  const inspectorByKey = new Map();
  for (const ins of doc.inspectors || []) {
    inspectorByKey.set(ins.key, ins);
  }

  function isGlossaryWorthy(ins) {
    if (!ins || !ins.kind) return false;
    if (ins.kind.parameter) return false;
    const key = ins.key || "";
    if (
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
          frag.appendChild(document.createTextNode(bb));
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
          cmd === "boldsymbol" || cmd === "mathrel"
        ) {
          const [arg, next] = readBalanced(tex, i);
          const span = document.createElement("span");
          span.className = "cadmo-op";
          if (cmd === "mathbf" || cmd === "boldsymbol") span.style.fontWeight = "600";
          if (cmd === "text" || cmd === "mathrm" || cmd === "mathsf" || cmd === "operatorname") {
            span.textContent = arg.replace(/\\_/g, "_");
          } else {
            span.appendChild(renderMathNodes(arg));
          }
          frag.appendChild(span);
          i = next;
          continue;
        }
        if (SYMBOL_MAP[cmd] !== undefined) {
          frag.appendChild(document.createTextNode(SYMBOL_MAP[cmd]));
          continue;
        }
        frag.appendChild(document.createTextNode(cmd));
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

  function renderMathSpan(tex, displayMode = false) {
    const el = document.createElement(displayMode ? "div" : "span");
    el.className = displayMode ? "cadmo-display-math" : "cadmo-math";
    el.dataset.latex = tex || "";
    if (window.katex && typeof window.katex.render === "function") {
      try {
        window.katex.render(tex || "", el, { displayMode, throwOnError: false });
        return el;
      } catch (_) {
        /* fallback below */
      }
    }
    el.appendChild(renderMathNodes(tex || ""));
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

  function renderMixedText(str) {
    const frag = document.createDocumentFragment();
    if (!str) return frag;
    const re = /\\\(([\s\S]*?)\\\)/g;
    let last = 0;
    let m;
    while ((m = re.exec(str)) !== null) {
      if (m.index > last) frag.appendChild(document.createTextNode(str.slice(last, m.index)));
      frag.appendChild(renderMathSpan(m[1], false));
      last = re.lastIndex;
    }
    if (last < str.length) frag.appendChild(document.createTextNode(str.slice(last)));
    return frag;
  }

  function renderInline(inl) {
    if (!inl || typeof inl !== "object") return document.createTextNode("");
    if (inl.text !== undefined) {
      const val = typeof inl.text === "string" ? inl.text : inl.text.value;
      return renderMixedText(val || "");
    }
    if (inl.emph !== undefined) {
      const val = typeof inl.emph === "string" ? inl.emph : inl.emph.value;
      return h("em", {}, val || "");
    }
    if (inl.inlineMath !== undefined) {
      const tex = typeof inl.inlineMath === "string" ? inl.inlineMath : inl.inlineMath.latex;
      return renderMathSpan(tex || "", false);
    }
    if (inl.displayMath !== undefined) {
      const obj = inl.displayMath;
      const tex = typeof obj === "string" ? obj : obj.latex;
      const punct = typeof obj === "object" && obj.punct ? obj.punct : "";
      return renderMathSpan((tex || "") + (punct ? "\\," + punct : ""), true);
    }
    if (inl.symbol !== undefined) {
      const sym = inl.symbol;
      const ins = inspectorByKey.get(sym.key);
      const isSelected = state.inspector && state.inspector.type === "symbol" &&
        state.inspector.item.key === sym.key;
      return h("button", {
        type: "button",
        class: "cadmo-sym",
        "aria-pressed": isSelected ? "true" : "false",
        onClick: () => {
          if (ins) {
            state.inspector = { type: "symbol", item: ins };
            renderAll();
          }
        }
      }, sym.isMath ? renderMathSpan(sym.display, false) : sym.display);
    }
    if (inl.citation !== undefined) {
      const c = inl.citation;
      return h("span", { title: c.detail || "" }, `[${c.label}]`);
    }
    return document.createTextNode("");
  }

  function renderInlines(arr) {
    const frag = document.createDocumentFragment();
    for (const item of arr || []) frag.appendChild(renderInline(item));
    return frag;
  }

  function projectNodes(nodes) {
    if (!Array.isArray(nodes)) return [];
    if (state.mode === "auditor") return nodes;
    const out = [];
    for (const n of nodes) {
      if (n.kind === "step" && n.isWrapper && Array.isArray(n.children) && n.children.length > 0) {
        out.push(...projectNodes(n.children));
      } else {
        out.push(n);
      }
    }
    return out;
  }

  function collectAllExpandableIds(nodes, out = []) {
    for (const n of nodes || []) {
      if (n.kind === "step" && Array.isArray(n.children) && n.children.length > 0) {
        out.push(n.id);
        collectAllExpandableIds(n.children, out);
      } else if (n.kind === "calcChain") {
        (n.steps || []).forEach((s, idx) => {
          if (Array.isArray(s.children) && s.children.length > 0) {
            out.push(`${n.id}-s${idx}`);
            collectAllExpandableIds(s.children, out);
          }
        });
      } else if (n.kind === "routineReceipt" && Array.isArray(n.details) && n.details.length > 0) {
        out.push(n.id);
        collectAllExpandableIds(n.details, out);
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
    const { leadIn = null, appendQed = false, depth = 0 } = opts;
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

    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      if (!node || node.kind === "figure") continue;

      if (node.kind === "flowNote") {
        flushPara(false);
        const p = h("p", { class: "cadmo-flow-note" }, node.text || "");
        out.push(p);
        continue;
      }

      if (node.kind === "routineReceipt") {
        // In Paper mode at top level, keep pure routine receipts quiet unless there's no other step
        if (state.mode === "paper" && depth === 0 && nodes.length > 1) continue;
        const hasDetails = Array.isArray(node.details) && node.details.length > 0;
        const isOpen = state.expanded.has(node.id);
        ensureLeadIn();
        paraChildren.push(
          h("span", { class: "cadmo-sent cadmo-routine" },
            hasDetails
              ? h("button", {
                  type: "button",
                  class: "cadmo-inline-toggle",
                  "aria-expanded": isOpen ? "true" : "false",
                  onClick: () => toggleId(node.id)
                }, isOpen ? "⊖" : "⊕")
              : null,
            `By ${node.summary || "routine algebra"}.`,
            renderGoalButton(node.goal, node.summary || "Routine step")
          )
        );
        if (hasDetails && isOpen) {
          flushPara(false);
          out.push(h("div", { class: "cadmo-expansion" },
            ...renderProofFlow(node.details, { depth: depth + 1 })
          ));
        }
        continue;
      }

      if (node.kind === "calcChain") {
        if (node.intro && node.intro.length > 0) {
          ensureLeadIn();
          paraChildren.push(
            h("span", { class: "cadmo-sent" },
              renderInlines(node.intro),
              renderGoalButton(node.goal, "Calculation target")
            )
          );
        } else if (leadIn && !usedLeadIn) {
          ensureLeadIn();
        }
        flushPara(false);
        const rows = [];
        (node.steps || []).forEach((item, idx) => {
          const st = item.step || {};
          const ch = projectNodes(item.children || []);
          const sid = `${node.id}-s${idx}`;
          const isOpen = state.expanded.has(sid);
          rows.push(
            h("tr", {},
              h("td", { class: "cadmo-calc-lhs" }, idx === 0 ? renderMathSpan(st.lhsLatex || "", false) : ""),
              h("td", { class: "cadmo-calc-rel" }, renderMathSpan(st.relationLatex || "=", false)),
              h("td", { class: "cadmo-calc-rhs" }, renderMathSpan(st.rhsLatex || "", false)),
              h("td", { class: "cadmo-calc-reason" },
                renderInlines(st.reason || []),
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
            rows.push(
              h("tr", { class: "cadmo-calc-expand-row" },
                h("td", { colspan: "4" },
                  h("div", { class: "cadmo-expansion" },
                    ...renderProofFlow(ch, { depth: depth + 1 })
                  )
                )
              )
            );
          }
        });
        out.push(h("div", { class: "cadmo-calc" },
          h("table", { class: "cadmo-calc-table" }, h("tbody", {}, ...rows))
        ));
        continue;
      }

      // Default: `step` — flows INLINE inside the current paragraph!
      const children = projectNodes(node.children || []);
      const hasChildren = children.length > 0;
      const isOpen = state.expanded.has(node.id);
      ensureLeadIn();
      const sent = h("span", { class: "cadmo-sent" + (node.isWrapper ? " is-wrapper" : "") },
        renderInlines(node.content || []),
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
      paraChildren.push(sent);

      // Only break out an indented expansion block if THIS sentence is currently expanded!
      if (hasChildren && isOpen) {
        flushPara(false);
        out.push(h("div", { class: "cadmo-expansion" },
          ...renderProofFlow(children, { depth: depth + 1 })
        ));
      }
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

  /* ------------------------------------------------------------------------
     Tufte Sidenote Margin: completely blank by default.
     Only renders what the reader explicitly requested.
     ------------------------------------------------------------------------ */
  function renderMargin(glossaryItems) {
    const items = [];

    if (state.inspector) {
      if (state.inspector.type === "symbol") {
        const ins = state.inspector.item;
        const kind = ins.kind || {};
        let kicker = "Symbol";
        const body = [];
        if (kind.interfaceTable) {
          kicker = "Interface";
          const it = kind.interfaceTable;
          if (it.domainLatex) body.push(h("p", {}, "Domain: ", renderMathSpan(it.domainLatex, false)));
          const rows = (it.ports || []).map((p) =>
            h("tr", {},
              h("td", {}, p.port),
              h("td", {}, renderMathSpan(p.queryLatex, false)),
              h("td", {}, renderMathSpan(p.replyLatex, false))
            )
          );
          if (rows.length > 0) {
            body.push(h("table", { class: "cadmo-inspector-table" },
              h("thead", {}, h("tr", {}, h("th", {}, "Port"), h("th", {}, "Query"), h("th", {}, "Reply"))),
              h("tbody", {}, ...rows)
            ));
          }
          if (it.budgetNote) body.push(h("p", {}, renderMixedText(it.budgetNote)));
        } else if (kind.dslPseudocode) {
          kicker = "System / Converter";
          const dp = kind.dslPseudocode;
          if (dp.header) body.push(h("p", {}, h("strong", {}, dp.header)));
          body.push(h("pre", { class: "cadmo-pseudocode" }, dp.body || dp.fullSource || ""));
        } else if (kind.ccDiagram) {
          kicker = "CC Assembly";
          const d = kind.ccDiagram;
          if (d.summaryLatex) body.push(renderMathSpan(d.summaryLatex, true));
        } else if (kind.mathDefinition) {
          kicker = "Definition";
          const md = kind.mathDefinition;
          if (md.proseSummary) body.push(h("p", {}, renderMixedText(md.proseSummary)));
          if (md.equationLatex) body.push(renderMathSpan(md.equationLatex, true));
        } else if (kind.witnessCard) {
          kicker = "Witness";
          const wc = kind.witnessCard;
          if (wc.title) body.push(h("p", {}, h("strong", {}, renderMixedText(wc.title))));
          const rows = (wc.rows || []).map(([k, v]) =>
            h("tr", {}, h("th", {}, k), h("td", {}, renderMathSpan(v, false)))
          );
          body.push(h("table", { class: "cadmo-inspector-table" }, h("tbody", {}, ...rows)));
        } else if (kind.parameter) {
          kicker = "Parameter";
          body.push(h("p", {}, renderMixedText(kind.parameter.roleDescription || "")));
        }

        items.push(h("section", { class: "cadmo-sidenote" },
          h("div", { class: "cadmo-sidenote-head" },
            h("div", {},
              h("div", { class: "cadmo-sidenote-kicker" }, kicker),
              h("h3", { class: "cadmo-sidenote-title" }, renderMathSpan(ins.display, false))
            ),
            h("button", {
              type: "button",
              class: "cadmo-close-btn",
              "aria-label": "Dismiss note",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "×")
          ),
          ...body,
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

  function renderEntry(entry, idx, suppressAmbient = false) {
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
          onClick: () => { state.inspector = { type: "axioms", entry }; renderAll(); }
        }, ax.hasSorry ? "sorry" : "axioms")
      ),
      (!suppressAmbient && entry.ambient)
        ? h("p", { class: "cadmo-ambient" },
            h("span", { class: "cadmo-ambient-label" }, "Setting."),
            renderInlines(entry.ambient.summary || [])
          )
        : null,
      h("div", { class: "cadmo-statement" },
        ...(entry.statement || []).map((para) => h("p", {}, renderInlines(para)))
      ),
      proofNodes.length > 0
        ? h("section", { class: "cadmo-proof" },
            ...renderProofFlow(entry.proof || [], { leadIn: "Proof.", appendQed: true, depth: 0 })
          )
        : null
    );
  }

  function renderAll() {
    document.documentElement.dataset.mode = state.mode;
    document.documentElement.dataset.theme = state.theme;

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
    const bodyNodes = [];
    if (firstAmbient) {
      bodyNodes.push(
        h("p", { class: "cadmo-chapter-setting" },
          h("span", { class: "cadmo-ambient-label" }, "Standing conventions. "),
          renderInlines(firstAmbient.summary || [])
        )
      );
    }
    let sectionNum = 0;
    entries.forEach((entry, idx) => {
      if (entry.sectionTitle) {
        sectionNum += 1;
        bodyNodes.push(
          h("div", { class: "cadmo-section-head" },
            h("h2", { class: "cadmo-section-title" },
              h("span", { class: "cadmo-section-num" }, `${sectionNum}.`),
              entry.sectionTitle
            ),
            entry.sectionIntro ? h("p", { class: "cadmo-section-intro" }, entry.sectionIntro) : null
          )
        );
      }
      bodyNodes.push(renderEntry(entry, idx, !!firstAmbient));
    });

    const shell = h("div", { class: "cadmo-shell" },
      h("main", { class: "cadmo-main" },
        header,
        ...bodyNodes
      ),
      renderMargin(glossaryItems)
    );

    rootEl.innerHTML = "";
    rootEl.appendChild(runningBar);
    rootEl.appendChild(shell);
  }

  renderAll();
})();
