/* ==========================================================================
   CADMO Interactive Proof Reader Controller
   Consumes the canonical Informalization.Core.Explanation.Document JSON.
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
    inspector: null, // { type: "symbol", item } | { type: "goal", goal, label } | { type: "axioms", entry }
    theme: "auto"
  };

  const inspectorByKey = new Map();
  for (const ins of doc.inspectors || []) {
    inspectorByKey.set(ins.key, ins);
  }

  /* ------------------------------------------------------------------------
     Readable offline math formatter (used directly and upgraded by KaTeX
     if KaTeX is available on the page).
     ------------------------------------------------------------------------ */
  /* Balanced-brace command replacer so nested `{...}` (like `\mathbf{1}_{P}`) never truncate. */
  function replaceBalanced1(str, cmd, fn) {
    let out = "";
    let i = 0;
    const prefix = cmd + "{";
    while (i < str.length) {
      const idx = str.indexOf(prefix, i);
      if (idx === -1) { out += str.slice(i); break; }
      out += str.slice(i, idx);
      let depth = 1;
      let j = idx + prefix.length;
      while (j < str.length && depth > 0) {
        if (str[j] === "{") depth++;
        else if (str[j] === "}") depth--;
        j++;
      }
      if (depth === 0) {
        const inner = str.slice(idx + prefix.length, j - 1);
        out += fn(replaceBalanced1(inner, cmd, fn));
        i = j;
      } else {
        out += prefix;
        i = idx + prefix.length;
      }
    }
    return out;
  }

  function replaceBalanced2(str, cmd, fn) {
    let out = "";
    let i = 0;
    const prefix = cmd + "{";
    while (i < str.length) {
      const idx = str.indexOf(prefix, i);
      if (idx === -1) { out += str.slice(i); break; }
      out += str.slice(i, idx);
      let d1 = 1, j = idx + prefix.length;
      while (j < str.length && d1 > 0) {
        if (str[j] === "{") d1++; else if (str[j] === "}") d1--;
        j++;
      }
      if (d1 === 0 && str[j] === "{") {
        const a1 = str.slice(idx + prefix.length, j - 1);
        let d2 = 1, k = j + 1;
        while (k < str.length && d2 > 0) {
          if (str[k] === "{") d2++; else if (str[k] === "}") d2--;
          k++;
        }
        if (d2 === 0) {
          const a2 = str.slice(j + 1, k - 1);
          out += fn(a1, a2);
          i = k;
          continue;
        }
      }
      out += prefix;
      i = idx + prefix.length;
    }
    return out;
  }

  function prettyFallbackMath(tex) {
    if (!tex) return "";
    let s = tex;
    s = replaceBalanced2(s, "\\frac", (a, b) => `(${a})/(${b})`);
    s = replaceBalanced2(s, "\\binom", (n, k) => `C(${n}, ${k})`);
    s = replaceBalanced1(s, "\\xrightarrow", (x) => `—[${x}]→`);
    s = replaceBalanced1(s, "\\simeq_", (x) => `≃[${x}]`);
    s = replaceBalanced1(s, "\\approx_", (x) => `≈[${x}]`);
    for (const cmd of ["\\mathcal", "\\mathrm", "\\mathbf", "\\boldsymbol", "\\operatorname", "\\mathsf", "\\text", "\\texttt", "\\mathrel"]) {
      s = replaceBalanced1(s, cmd, (x) => x);
    }
    return s
      .replace(/\\mathbb\{R\}_\{\\ge 0\}\^\{\\infty\}/g, "ℝ≥0∞")
      .replace(/\\mathbb\{R\}_\{\\ge 0\}/g, "ℝ≥0")
      .replace(/\\mathbb\{R\}/g, "ℝ")
      .replace(/\\mathbb\{N\}/g, "ℕ")
      .replace(/\\mathbb\{Z\}/g, "ℤ")
      .replace(/\\mathbb\{Q\}/g, "ℚ")
      .replace(/\\varepsilon/g, "ε")
      .replace(/\\epsilon/g, "ε")
      .replace(/\\Delta/g, "Δ")
      .replace(/\\Gamma/g, "Γ")
      .replace(/\\Pi/g, "Π")
      .replace(/\\Sigma/g, "Σ")
      .replace(/\\Phi/g, "Φ")
      .replace(/\\pi\b/g, "π")
      .replace(/\\sigma\b/g, "σ")
      .replace(/\\kappa\b/g, "κ")
      .replace(/\\alpha\b/g, "α")
      .replace(/\\beta\b/g, "β")
      .replace(/\\gamma\b/g, "γ")
      .replace(/\\delta\b/g, "δ")
      .replace(/\\rho\b/g, "ρ")
      .replace(/\\tau\b/g, "τ")
      .replace(/\\phi\b/g, "φ")
      .replace(/\\varphi\b/g, "φ")
      .replace(/\\psi\b/g, "ψ")
      .replace(/\\iota\b/g, "ι")
      .replace(/\\theta\b/g, "θ")
      .replace(/\\lambda\b/g, "λ")
      .replace(/\\mu\b/g, "μ")
      .replace(/\\nu\b/g, "ν")
      .replace(/\\ell\b/g, "ℓ")
      .replace(/\\star\b/g, "★")
      .replace(/\\varnothing\b/g, "∅")
      .replace(/\\emptyset\b/g, "∅")
      .replace(/\\parallel/g, "∥")
      .replace(/\\otimes\b/g, "⊗")
      .replace(/\\oplus\b/g, "⊕")
      .replace(/\\equiv\b/g, "≡")
      .replace(/\\simeq\b/g, "≃")
      .replace(/\\approx\b/g, "≈")
      .replace(/\\le\b/g, "≤")
      .replace(/\\ge\b/g, "≥")
      .replace(/\\ne\b/g, "≠")
      .replace(/\\neq\b/g, "≠")
      .replace(/\\implies\b/g, "⇒")
      .replace(/\\iff\b/g, "⇔")
      .replace(/\\in\b/g, "∈")
      .replace(/\\notin\b/g, "∉")
      .replace(/\\subseteq\b/g, "⊆")
      .replace(/\\times\b/g, "×")
      .replace(/\\cdot\b/g, "·")
      .replace(/\\circ\b/g, "∘")
      .replace(/\\to\b/g, "→")
      .replace(/\\mapsto\b/g, "↦")
      .replace(/\\forall\b/g, "∀")
      .replace(/\\exists\b/g, "∃")
      .replace(/\\land\b/g, "∧")
      .replace(/\\wedge\b/g, "∧")
      .replace(/\\lor\b/g, "∨")
      .replace(/\\vee\b/g, "∨")
      .replace(/\\neg\b/g, "¬")
      .replace(/\\sum\b/g, "∑")
      .replace(/\\prod\b/g, "∏")
      .replace(/\\infty\b/g, "∞")
      .replace(/\\Pr\b/g, "Pr")
      .replace(/\\min\b/g, "min")
      .replace(/\\max\b/g, "max")
      .replace(/\\left\(/g, "(")
      .replace(/\\right\)/g, ")")
      .replace(/\\left\[/g, "[")
      .replace(/\\right\]/g, "]")
      .replace(/\\left\|/g, "|")
      .replace(/\\right\|/g, "|")
      .replace(/\\left\\\{/g, "{")
      .replace(/\\right\\\}/g, "}")
      .replace(/\\\{/g, "{")
      .replace(/\\\}/g, "}")
      .replace(/\\,/g, " ")
      .replace(/\\;/g, " ")
      .replace(/\\!/g, "")
      .replace(/\\_/g, "_")
      .replace(/\^\{\*\}/g, "*")
      .replace(/_\{([A-Za-z0-9']+?)\}/g, "_$1")
      .replace(/\^\{([A-Za-z0-9'+-]+?)\}/g, "^$1");
  }

  function renderMathSpan(tex, displayMode = false) {
    const el = document.createElement(displayMode ? "div" : "span");
    el.className = displayMode ? "cadmo-display-math" : "cadmo-math";
    el.dataset.latex = tex;
    if (window.katex && typeof window.katex.render === "function") {
      try {
        window.katex.render(tex, el, { displayMode, throwOnError: false });
        return el;
      } catch (_) {
        /* fallback below */
      }
    }
    el.textContent = prettyFallbackMath(tex);
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

  /* Parse mixed prose containing inline \(...\) math delimiters into rich DOM nodes. */
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
      const btn = h("button", {
        type: "button",
        class: "cadmo-sym",
        "aria-pressed": isSelected ? "true" : "false",
        title: ins ? `Inspect ${sym.display}` : sym.display,
        onClick: () => {
          if (ins) {
            state.inspector = { type: "symbol", item: ins };
            renderAll();
          }
        }
      }, sym.isMath ? renderMathSpan(sym.display, false) : sym.display);
      return btn;
    }
    if (inl.citation !== undefined) {
      const c = inl.citation;
      return h("span", { class: "cadmo-citation", title: c.detail || "" }, `[${c.label}]`);
    }
    return document.createTextNode("");
  }

  function renderInlines(arr) {
    const frag = document.createDocumentFragment();
    for (const item of arr || []) frag.appendChild(renderInline(item));
    return frag;
  }

  /* ------------------------------------------------------------------------
     Paper mode smart wrapper inlining: in Paper mode, a `step` marked
     `isWrapper: true` with non-empty children transparently surfaces its
     children instead of cluttering Level 0 with a Lean forwarding wrapper.
     Auditor mode shows every declaration boundary verbatim.
     ------------------------------------------------------------------------ */
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
      title: "Inspect checked Lean goal state",
      onClick: () => {
        state.inspector = { type: "goal", goal, label };
        renderAll();
      }
    }, "⊢");
  }

  function renderDiagramHtml(html) {
    const wrap = h("div", { class: "cadmo-figure" });
    wrap.innerHTML = html;
    return wrap;
  }

  function renderProofNode(node) {
    if (!node) return null;

    if (node.kind === "flowNote") {
      return h("aside", { class: "cadmo-flow-note" },
        h("span", { class: "cadmo-flow-badge" }, "Note"),
        node.text || ""
      );
    }

    if (node.kind === "figure") {
      const fig = h("figure", { class: "cadmo-figure" });
      const body = h("div", {});
      body.innerHTML = node.html || "";
      fig.appendChild(body);
      if (node.caption && node.caption.length > 0) {
        fig.appendChild(h("figcaption", { class: "cadmo-figure-caption" }, renderInlines(node.caption)));
      }
      return fig;
    }

    if (node.kind === "routineReceipt") {
      const hasDetails = Array.isArray(node.details) && node.details.length > 0;
      const isOpen = state.expanded.has(node.id);
      const chip = h("div", { class: "cadmo-routine" },
        hasDetails
          ? h("button", {
              type: "button",
              class: "cadmo-toggle",
              "aria-expanded": isOpen ? "true" : "false",
              onClick: () => { toggleId(node.id); }
            }, isOpen ? "⊖" : "⊕")
          : null,
        h("span", { class: "cadmo-routine-chip" },
          `${node.summary || "Routine calculation"} (${node.stepCount || 1} checked)`
        ),
        renderGoalButton(node.goal, node.summary || "Routine step")
      );
      if (hasDetails && isOpen) {
        const box = h("div", { class: "cadmo-children" },
          ...projectNodes(node.details).map(renderProofNode)
        );
        return h("div", { class: "cadmo-node" }, chip, box);
      }
      return h("div", { class: "cadmo-node" }, chip);
    }

    if (node.kind === "calcChain") {
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
              ch.length > 0
                ? h("button", {
                    type: "button",
                    class: "cadmo-toggle",
                    "aria-expanded": isOpen ? "true" : "false",
                    title: isOpen ? "Collapse step justification" : "Expand step justification",
                    onClick: () => { toggleId(sid); }
                  }, isOpen ? "⊖" : "⊕")
                : null,
              " ",
              renderInlines(st.reason || [])
            )
          )
        );
        if (ch.length > 0 && isOpen) {
          rows.push(
            h("tr", { class: "cadmo-calc-expand-row" },
              h("td", { colspan: "4" },
                st.diagramHtml ? renderDiagramHtml(st.diagramHtml) : null,
                h("div", { class: "cadmo-children" }, ...ch.map(renderProofNode))
              )
            )
          );
        }
      });
      return h("div", { class: "cadmo-calc" },
        node.intro && node.intro.length > 0
          ? h("p", { class: "cadmo-calc-intro" },
              renderInlines(node.intro),
              renderGoalButton(node.goal, "Calculation target")
            )
          : null,
        h("table", { class: "cadmo-calc-table" }, h("tbody", {}, ...rows))
      );
    }

    // Default: `step`
    const children = projectNodes(node.children || []);
    const hasChildren = children.length > 0;
    const isOpen = state.expanded.has(node.id);
    return h("div", { class: "cadmo-node" + (node.isWrapper ? " is-wrapper" : "") },
      h("div", { class: "cadmo-node-row" },
        hasChildren
          ? h("button", {
              type: "button",
              class: "cadmo-toggle",
              "aria-expanded": isOpen ? "true" : "false",
              title: isOpen ? "Collapse subproof" : "Expand subproof",
              onClick: () => { toggleId(node.id); }
            }, isOpen ? "⊖" : "⊕")
          : h("span", { class: "cadmo-toggle-spacer", "aria-hidden": "true" }),
        h("div", { class: "cadmo-node-body" },
          renderInlines(node.content || []),
          node.isWrapper ? h("span", { class: "cadmo-wrapper-tag" }, "wrapper") : null,
          node.originDecl ? h("span", { class: "cadmo-origin-tag" }, node.originDecl) : null,
          renderGoalButton(node.goal, node.originDecl || "Proof step")
        )
      ),
      node.diagramHtml ? renderDiagramHtml(node.diagramHtml) : null,
      hasChildren
        ? h("div", { class: "cadmo-children", hidden: !isOpen },
            ...children.map(renderProofNode)
          )
        : null
    );
  }

  function toggleId(id) {
    if (state.expanded.has(id)) state.expanded.delete(id);
    else state.expanded.add(id);
    renderAll();
  }

  /* ------------------------------------------------------------------------
     Type-Aware Margin Inspector (Symbols, Goal States, Axiom Footprint)
     ------------------------------------------------------------------------ */
  function renderInspectorPanel() {
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
          if (it.domainLatex) {
            body.push(h("p", {}, "Domain: ", renderMathSpan(it.domainLatex, false)));
          }
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
          if (it.budgetNote) body.push(h("p", {}, it.budgetNote));
        } else if (kind.dslPseudocode) {
          kicker = "System / Converter";
          const dp = kind.dslPseudocode;
          if (dp.header) body.push(h("p", {}, h("strong", {}, dp.header)));
          body.push(h("pre", { class: "cadmo-pseudocode" }, dp.body || dp.fullSource || ""));
        } else if (kind.ccDiagram) {
          kicker = "CC Assembly";
          const d = kind.ccDiagram;
          if (d.summaryLatex) body.push(renderMathSpan(d.summaryLatex, true));
          if (d.svgOrHtml) body.push(renderDiagramHtml(d.svgOrHtml));
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

        const leanDetails = h("details", { class: "cadmo-lean-details" },
          h("summary", {}, "Exact Lean signature"),
          h("div", { class: "cadmo-lean-code" },
            (ins.leanName ? `${ins.leanName} :\n` : "") + (ins.leanType || "")
          )
        );

        items.push(h("section", { class: "cadmo-inspector-card" },
          h("div", { class: "cadmo-inspector-head" },
            h("div", {},
              h("div", { class: "cadmo-inspector-kicker" }, kicker),
              h("h3", { class: "cadmo-inspector-title" }, renderMathSpan(ins.display, false))
            ),
            h("button", {
              type: "button",
              class: "cadmo-btn",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "Close")
          ),
          ...body,
          leanDetails
        ));
      } else if (state.inspector.type === "goal") {
        const g = state.inspector.goal;
        const ctxItems = (g.context || []).map((c) =>
          h("li", {},
            c.name ? h("strong", {}, renderMixedText(c.name), ": ") : null,
            renderMixedText(c.description || "")
          )
        );
        items.push(h("section", { class: "cadmo-inspector-card" },
          h("div", { class: "cadmo-inspector-head" },
            h("div", {},
              h("div", { class: "cadmo-inspector-kicker" }, "Checked Proof State"),
              h("h3", { class: "cadmo-inspector-title" }, state.inspector.label || "Goal")
            ),
            h("button", {
              type: "button",
              class: "cadmo-btn",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "Close")
          ),
          ctxItems.length > 0
            ? h("div", {},
                h("div", { class: "cadmo-inspector-kicker" }, "Context"),
                h("ul", { class: "cadmo-goal-ctx" }, ...ctxItems)
              )
            : null,
          h("div", { class: "cadmo-inspector-kicker" }, "Goal"),
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
        items.push(h("section", { class: "cadmo-inspector-card" },
          h("div", { class: "cadmo-inspector-head" },
            h("div", {},
              h("div", { class: "cadmo-inspector-kicker" }, "Kernel Axiom Audit"),
              h("h3", { class: "cadmo-inspector-title" }, e.title || e.declaration)
            ),
            h("button", {
              type: "button",
              class: "cadmo-btn",
              onClick: () => { state.inspector = null; renderAll(); }
            }, "Close")
          ),
          h("p", {}, ax.hasSorry
            ? "Warning: this declaration depends on sorryAx."
            : "Verified kernel proof with standard Lean axioms only."),
          h("div", { class: "cadmo-lean-code" },
            `Declaration: ${e.declaration}\nAxioms:\n` +
            ((ax.axioms && ax.axioms.length > 0) ? ax.axioms.map((a) => `  • ${a}`).join("\n") : "  (none)")
          )
        ));
      }
    } else {
      items.push(h("div", { class: "cadmo-inspector-card" },
        h("div", { class: "cadmo-inspector-kicker" }, "Interactive Inspector"),
        h("p", { style: "margin:0.45rem 0 0;color:var(--cadmo-ink-soft);" },
          "Click any underlined symbol to inspect its interface ports, pseudocode, or definition; " +
          "click ⊕ to descend into a proof step, or ⊢ to view the checked Lean proof state."
        )
      ));
    }

    if ((doc.inspectors || []).length > 0) {
      items.push(h("div", { class: "cadmo-symbol-index" },
        h("h4", {}, "Symbols & Definitions"),
        h("div", { class: "cadmo-symbol-chips" },
          ...(doc.inspectors || []).map((ins) =>
            h("button", {
              type: "button",
              class: "cadmo-symbol-chip",
              onClick: () => { state.inspector = { type: "symbol", item: ins }; renderAll(); }
            }, renderMathSpan(ins.display, false))
          )
        )
      ));
    }
    return h("aside", { class: "cadmo-margin", "aria-label": "Inspector margin" }, ...items);
  }

  function renderEntry(entry) {
    const ax = entry.axioms || { axioms: [], hasSorry: false };
    const proofNodes = projectNodes(entry.proof || []);
    return h("article", { class: "cadmo-entry", id: `decl-${entry.declaration}` },
      h("header", { class: "cadmo-entry-head" },
        h("h2", { class: "cadmo-entry-heading" },
          h("span", { class: "cadmo-entry-kind" }, entry.header || "Theorem"),
          entry.title ? h("span", { class: "cadmo-entry-title" }, `(${entry.title}).`) : null
        ),
        h("div", { class: "cadmo-entry-meta" },
          h("button", {
            type: "button",
            class: "cadmo-axiom-pill" + (ax.hasSorry ? " has-sorry" : ""),
            onClick: () => { state.inspector = { type: "axioms", entry }; renderAll(); }
          }, ax.hasSorry ? "⚠ sorry" : `✓ ${(ax.axioms || []).length} axioms`)
        )
      ),
      entry.ambient
        ? h("div", { class: "cadmo-ambient" },
            h("span", { class: "cadmo-ambient-label" }, "Setting."),
            renderInlines(entry.ambient.summary || [])
          )
        : null,
      h("div", { class: "cadmo-statement" },
        ...(entry.statement || []).map((para) => h("p", {}, renderInlines(para)))
      ),
      entry.diagramHtml ? renderDiagramHtml(entry.diagramHtml) : null,
      proofNodes.length > 0
        ? h("section", { class: "cadmo-proof" },
            h("span", { class: "cadmo-proof-lead" }, "Proof."),
            ...proofNodes.map(renderProofNode),
            h("div", { class: "cadmo-qed", "aria-hidden": "true" }, "□")
          )
        : null
    );
  }

  function renderAll() {
    document.documentElement.dataset.mode = state.mode;
    if (state.theme === "light" || state.theme === "dark") {
      document.documentElement.dataset.theme = state.theme;
    } else {
      delete document.documentElement.dataset.theme;
    }

    const toolbar = h("nav", { class: "cadmo-toolbar", "aria-label": "Document controls" },
      h("div", { class: "cadmo-toolbar-inner" },
        h("div", { class: "cadmo-running-head" }, doc.title || "Constructive Cryptography"),
        h("div", { class: "cadmo-controls" },
          h("div", { class: "cadmo-segmented", role: "group", "aria-label": "Disclosure mode" },
            h("button", {
              type: "button",
              "aria-pressed": state.mode === "paper" ? "true" : "false",
              onClick: () => { state.mode = "paper"; renderAll(); }
            }, "Paper"),
            h("button", {
              type: "button",
              "aria-pressed": state.mode === "auditor" ? "true" : "false",
              onClick: () => { state.mode = "auditor"; renderAll(); }
            }, "Auditor")
          ),
          h("button", {
            type: "button",
            class: "cadmo-btn",
            onClick: () => {
              for (const e of doc.entries || []) {
                for (const id of collectAllExpandableIds(e.proof || [])) state.expanded.add(id);
              }
              renderAll();
            }
          }, "Expand all"),
          h("button", {
            type: "button",
            class: "cadmo-btn",
            onClick: () => { state.expanded.clear(); renderAll(); }
          }, "Collapse all"),
          h("button", {
            type: "button",
            class: "cadmo-btn",
            onClick: () => {
              state.theme = state.theme === "dark" ? "light" : "dark";
              renderAll();
            }
          }, state.theme === "dark" ? "Light ink" : "Dark ink")
        )
      )
    );

    const header = h("header", { class: "cadmo-doc-header" },
      h("div", { class: "cadmo-kicker" }, "Constructive Cryptography · Checked Informalization"),
      h("h1", { class: "cadmo-doc-title" }, doc.title || "Untitled Document"),
      doc.subtitle ? h("p", { class: "cadmo-doc-subtitle" }, doc.subtitle) : null
    );

    const shell = h("div", { class: "cadmo-shell" },
      h("main", { class: "cadmo-main" },
        header,
        ...(doc.entries || []).map(renderEntry)
      ),
      renderInspectorPanel()
    );

    rootEl.innerHTML = "";
    rootEl.appendChild(toolbar);
    rootEl.appendChild(shell);
  }

  renderAll();
})();
