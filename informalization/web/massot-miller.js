(function () {
  'use strict';

  function mountInformalization(mountNode, declarations, options) {
  if (!mountNode || !Array.isArray(declarations)) return null;
  options = options || {};
  mountNode.classList.add('informalization-mount');
  var tooltipRoot = options.tooltipRoot || document.body;

  var currentGoal = null;
  var renderedGoals = [];
  var highlightAfterRender = null;
  var serial = 0;
  var hoverSerial = 0;
  var hoverLabelCache = Object.create(null);
  var activeTooltip = null;
  var tooltipHideTimer = null;

  function elt(tag, className) {
    var node = document.createElement(tag);
    if (className) node.className = className;
    return node;
  }

  function text(value) {
    return document.createTextNode(value == null ? '' : String(value));
  }

  function cancelTooltipHide() {
    if (tooltipHideTimer != null) window.clearTimeout(tooltipHideTimer);
    tooltipHideTimer = null;
  }

  function hideTooltip(tip) {
    cancelTooltipHide();
    if (!tip) return;
    tip.classList.remove('tooltip-visible', 'tooltip-measuring');
    if (activeTooltip === tip) activeTooltip = null;
  }

  function positionTooltip(anchor, tip) {
    if (!anchor || !tip || !anchor.isConnected || !tip.isConnected) return;
    var padding = 12;
    var gap = 8;
    var anchorRect = anchor.getBoundingClientRect();
    if (anchorRect.bottom < 0 || anchorRect.top > window.innerHeight) {
      hideTooltip(tip);
      return;
    }
    tip.classList.add('tooltip-visible', 'tooltip-measuring');
    tip.style.left = padding + 'px';
    tip.style.top = padding + 'px';
    var tipRect = tip.getBoundingClientRect();
    var left = anchorRect.left + anchorRect.width / 2 - tipRect.width / 2;
    left = Math.max(padding, Math.min(left, window.innerWidth - tipRect.width - padding));
    var below = anchorRect.bottom + gap;
    var above = anchorRect.top - gap - tipRect.height;
    var top = below + tipRect.height <= window.innerHeight - padding ? below : above;
    top = Math.max(padding, Math.min(top, window.innerHeight - tipRect.height - padding));
    tip.style.left = Math.round(left) + 'px';
    tip.style.top = Math.round(top) + 'px';
    tip.classList.remove('tooltip-measuring');
  }

  function showTooltip(anchor, tip) {
    cancelTooltipHide();
    if (activeTooltip && activeTooltip !== tip) hideTooltip(activeTooltip);
    activeTooltip = tip;
    positionTooltip(anchor, tip);
  }

  function scheduleTooltipHide(anchor, tip) {
    cancelTooltipHide();
    tooltipHideTimer = window.setTimeout(function () {
      if (document.activeElement === anchor || tip.matches(':hover')) return;
      hideTooltip(tip);
    }, 120);
  }

  function attachFloatingTooltip(anchor, tip) {
    if (!tip.id) tip.id = 'hover-' + hoverSerial++;
    tip.classList.add('floating-tooltip');
    tip.__anchor = anchor;
    anchor.setAttribute('aria-describedby', tip.id);
    anchor.addEventListener('mouseenter', function () { showTooltip(anchor, tip); });
    anchor.addEventListener('mouseleave', function () { scheduleTooltipHide(anchor, tip); });
    anchor.addEventListener('focus', function () { showTooltip(anchor, tip); });
    anchor.addEventListener('blur', function () { scheduleTooltipHide(anchor, tip); });
    anchor.addEventListener('keydown', function (event) {
      if (event.key === 'Escape') { anchor.blur(); hideTooltip(tip); }
    });
    tip.addEventListener('mouseenter', cancelTooltipHide);
    tip.addEventListener('mouseleave', function () { scheduleTooltipHide(anchor, tip); });
    tooltipRoot.appendChild(tip);
  }

  function clearFloatingTooltips() {
    hideTooltip(activeTooltip);
    tooltipRoot.querySelectorAll('.floating-tooltip').forEach(function (tip) { tip.remove(); });
  }

  function repositionActiveTooltip() {
    if (activeTooltip) positionTooltip(activeTooltip.__anchor, activeTooltip);
  }

  function decodeLeanText(value) {
    return String(value)
      .replace(/\\textbackslash\{\}/g, '\\')
      .replace(/\\textasciitilde\{\}/g, '~')
      .replace(/\\\^\{\}/g, '^')
      .replace(/\\([{}_#$%&])/g, '$1');
  }

  // Compatibility with documents generated before exact source received its
  // own inert transport marker.
  function renderLeanFallback(parent, source) {
    var prefix = '\\operatorname{Lean}\\left[\\text{';
    var suffix = '}\\right]';
    if (!source.startsWith(prefix) || !source.endsWith(suffix)) return false;
    var wrapper = elt('span', 'lean-fallback');
    var label = elt('span', 'lean-fallback-label');
    label.appendChild(text('Lean'));
    var code = elt('code', 'lean-fallback-code');
    code.appendChild(text(decodeLeanText(source.slice(prefix.length, -suffix.length))));
    wrapper.appendChild(label);
    wrapper.appendChild(text('['));
    wrapper.appendChild(code);
    wrapper.appendChild(text(']'));
    parent.appendChild(wrapper);
    return true;
  }

  var rawSourcePrefix = '\\informalizationRaw{';

  function rawSourceFragments(source) {
    var chunks = [];
    var cursor = 0;
    while (cursor < source.length) {
      var start = source.indexOf(rawSourcePrefix, cursor);
      if (start < 0) break;
      var jsonStart = start + rawSourcePrefix.length;
      if (source[jsonStart] !== '"') return null;
      var index = jsonStart + 1;
      var escaped = false;
      for (; index < source.length; index++) {
        var character = source[index];
        if (escaped) { escaped = false; continue; }
        if (character === '\\') { escaped = true; continue; }
        if (character === '"') break;
      }
      if (index >= source.length || source[index + 1] !== '}') return null;
      var raw;
      try { raw = JSON.parse(source.slice(jsonStart, index + 1)); }
      catch (_err) { return null; }
      if (start > cursor) chunks.push({ kind: 'latex', value: source.slice(cursor, start) });
      chunks.push({ kind: 'source', value: raw });
      cursor = index + 2;
    }
    if (!chunks.length) return null;
    if (cursor < source.length) chunks.push({ kind: 'latex', value: source.slice(cursor) });
    return chunks;
  }

  function renderRawSource(parent, source, referenceHovers) {
    var chunks = rawSourceFragments(source);
    if (!chunks) return false;
    parent.classList.add('mixed-source-math');
    chunks.forEach(function (chunk) {
      if (chunk.kind === 'source') {
        var code = elt('code', 'inert-source-fragment');
        code.appendChild(text(chunk.value));
        parent.appendChild(code);
      } else if (chunk.value) {
        var math = elt('span', 'latex-fragment');
        typeset(math, chunk.value, false, referenceHovers);
        parent.appendChild(math);
      }
    });
    return true;
  }

  function typeset(parent, source, display, referenceHovers) {
    source = String(source);
    if (renderRawSource(parent, source, referenceHovers || [])) return;
    if (renderLeanFallback(parent, source)) return;
    if (window.katex && typeof window.katex.render === 'function') {
      try {
        window.katex.render(source, parent, {
          displayMode: !!display,
          throwOnError: true,
          trust: false,
          strict: 'ignore',
          maxExpand: 1000
        });
        annotateMathReferences(parent, referenceHovers || []);
        return;
      } catch (_err) { /* retain the exact source below */ }
    }
    var fallback = elt('code', 'math-source-fallback');
    fallback.appendChild(text(source));
    parent.appendChild(fallback);
  }

  function normalizedMathText(value) {
    return String(value == null ? '' : value)
      .replace(/[\u200b-\u200d\u2060\u2061\ufeff]/gi, '')
      .replace(/\s+/g, '');
  }

  function renderedHoverLabel(latex) {
    latex = String(latex || '');
    if (!latex) return '';
    if (Object.prototype.hasOwnProperty.call(hoverLabelCache, latex)) {
      return hoverLabelCache[latex];
    }
    var label = latex;
    if (window.katex && typeof window.katex.render === 'function') {
      try {
        var scratch = elt('span');
        window.katex.render(latex, scratch, {
          displayMode: false,
          throwOnError: true,
          trust: false,
          strict: 'ignore',
          maxExpand: 1000
        });
        var html = scratch.querySelector('.katex-html');
        if (html) label = html.textContent;
      } catch (_err) { /* use the inert source label */ }
    }
    label = normalizedMathText(label);
    hoverLabelCache[latex] = label;
    return label;
  }

  function leanHoverTooltip(hover) {
    var tip = elt('span', 'tooltip-content lean-hover-content');
    tip.setAttribute('role', 'tooltip');
    tip.id = 'lean-hover-' + hoverSerial++;

    if (hover.description) {
      var description = elt('span', 'lean-hover-description');
      description.appendChild(text(hover.description));
      tip.appendChild(description);
    }

    var signature = elt('span', 'lean-hover-signature');
    var name = elt('code'); name.appendChild(text(hover.name || ''));
    var type = elt('code'); type.appendChild(text(hover.type || ''));
    signature.appendChild(name);
    signature.appendChild(text(' : '));
    signature.appendChild(type);
    tip.appendChild(signature);

    if (hover.explicit && hover.explicit !== hover.name) {
      var explicit = elt('span', 'lean-hover-explicit');
      explicit.appendChild(text('Expression: '));
      var explicitCode = elt('code'); explicitCode.appendChild(text(hover.explicit));
      explicit.appendChild(explicitCode);
      tip.appendChild(explicit);
    }

    if (hover.documentation) {
      var documentation = elt('span', 'lean-hover-documentation');
      documentation.appendChild(text(hover.documentation));
      tip.appendChild(documentation);
    }
    return tip;
  }

  function attachLeanHover(anchor, hover) {
    if (!anchor || !hover || anchor.classList.contains('lean-reference')) return;
    anchor.classList.add('with-tooltip', 'lean-reference');
    anchor.tabIndex = 0;
    var tip = leanHoverTooltip(hover);
    attachFloatingTooltip(anchor, tip);
  }

  function annotateMathReferences(parent, referenceHovers) {
    if (!referenceHovers || !referenceHovers.length) return;
    var math = parent.querySelector('.katex-html');
    if (!math) return;
    var selector = '.mord, .mop, .mrel, .mbin';
    var atoms = Array.prototype.slice.call(math.querySelectorAll(selector)).map(function (node) {
      return { node: node, value: normalizedMathText(node.textContent) };
    });
    var entries = referenceHovers.map(function (hover) {
      return { hover: hover, value: renderedHoverLabel(hover.latex) };
    }).filter(function (entry) { return !!entry.value; });
    entries.sort(function (left, right) { return right.value.length - left.value.length; });
    var claimed = [];
    entries.forEach(function (entry) {
      atoms.forEach(function (atom) {
        if (atom.value !== entry.value) return;
        var parentAtom = atom.node.parentElement && atom.node.parentElement.closest(selector);
        if (parentAtom && parentAtom !== atom.node &&
            normalizedMathText(parentAtom.textContent) !== entry.value &&
            atom.node.parentElement === parentAtom) return;
        if (claimed.some(function (node) {
          return node === atom.node || node.contains(atom.node) || atom.node.contains(node);
        })) return;
        attachLeanHover(atom.node, entry.hover);
        claimed.push(atom.node);
      });
    });
  }

  // InformalLean strings interleave prose with \(...\) and \[...\].  Parse
  // only those fixed delimiters; no string is ever interpreted as HTML.
  function richText(source, referenceHovers) {
    var frag = document.createDocumentFragment();
    var s = String(source == null ? '' : source);
    var pos = 0;
    while (pos < s.length) {
      var inline = s.indexOf('\\(', pos);
      var block = s.indexOf('\\[', pos);
      var start;
      var display;
      if (inline < 0) { start = block; display = true; }
      else if (block < 0 || inline < block) { start = inline; display = false; }
      else { start = block; display = true; }
      if (start < 0) {
        frag.appendChild(text(s.slice(pos)));
        break;
      }
      if (start > pos) frag.appendChild(text(s.slice(pos, start)));
      var close = display ? '\\]' : '\\)';
      var end = s.indexOf(close, start + 2);
      if (end < 0) {
        frag.appendChild(text(s.slice(start)));
        break;
      }
      var math = elt(display ? 'span' : 'span', display ? 'math-display' : 'math-inline');
      math.setAttribute('data-source-math', s.slice(start, end + 2));
      typeset(math, s.slice(start + 2, end), display, referenceHovers || []);
      frag.appendChild(math);
      pos = end + 2;
    }
    return frag;
  }

  function Builder(className) {
    this.fragment = document.createDocumentFragment();
    this.paragraph = null;
    this.className = className || '';
  }

  Builder.prototype.ensureParagraph = function () {
    if (!this.paragraph) {
      this.paragraph = elt('p', this.className);
      this.fragment.appendChild(this.paragraph);
    }
    return this.paragraph;
  };

  Builder.prototype.inline = function (node) {
    this.ensureParagraph().appendChild(node);
  };

  Builder.prototype.breakParagraph = function () {
    this.paragraph = null;
  };

  Builder.prototype.block = function (node) {
    this.breakParagraph();
    if (this.className) {
      this.className.split(/\s+/).filter(Boolean).forEach(function (className) {
        node.classList.add(className);
      });
    }
    this.fragment.appendChild(node);
    this.breakParagraph();
  };

  function appendInlineFragment(parent, fragment) {
    while (fragment.firstChild) {
      var child = fragment.firstChild;
      if (child.nodeType === 1 && child.tagName === 'P') {
        while (child.firstChild) parent.appendChild(child.firstChild);
        child.remove();
      } else {
        parent.appendChild(child);
      }
    }
  }

  function renderTooltip(node, builder, context) {
    var anchor = elt('span', 'with-tooltip');
    var inner = new Builder(context.className);
    processExplanation(node.value, inner, context);
    appendInlineFragment(anchor, inner.fragment);
    anchor.tabIndex = 0;
    var tip = elt('span', 'tooltip-content');
    tip.setAttribute('role', 'tooltip');
    tip.appendChild(richText(node.tooltip, []));
    attachFloatingTooltip(anchor, tip);
    builder.inline(anchor);
  }

  function mergedReferenceHovers(primary, inherited) {
    var result = [];
    (primary || []).concat(inherited || []).forEach(function (hover) {
      if (!hover || !hover.latex) return;
      if (!result.some(function (known) { return known.latex === hover.latex; })) {
        result.push(hover);
      }
    });
    return result;
  }

  function renderGoalButton(goal, builder) {
    renderedGoals.push(goal);
    var button = elt('button', 'goal-button');
    button.type = 'button';
    button.textContent = '⬭';
    button.setAttribute('aria-controls', 'proof-state-pane');
    button.setAttribute('aria-label', 'Show current proof state');
    button.setAttribute('aria-pressed', currentGoal === goal ? 'true' : 'false');
    if (currentGoal === goal) {
      button.classList.add('goal-button-active');
      button.setAttribute('aria-label', 'Hide current proof state');
    }
    button.addEventListener('click', function (event) {
      event.stopPropagation();
      currentGoal = currentGoal === goal ? null : goal;
      renderGoalPane();
      renderDocumentPane();
    });
    builder.inline(text(' '));
    builder.inline(button);
    builder.inline(text(' '));
  }

  function renderReplacement(node, builder, context) {
    var id = context.name + '-replacement-' + serial++;
    var selected = node.expanded
      ? [node.preReplace, node.replace, node.postReplace]
      : [node.preValue, node.value, node.postValue];
    var button = elt('button', 'explanation-refinement-button');
    button.type = 'button';
    button.textContent = node.expanded ? '⊖' : '⊕';
    button.setAttribute('aria-expanded', node.expanded ? 'true' : 'false');
    button.setAttribute('aria-label', node.expanded ? 'Use shorter explanation' : 'Show further proof');
    button.addEventListener('click', function (event) {
      event.stopPropagation();
      node.expanded = !node.expanded;
      highlightAfterRender = id;
      renderDocumentPane();
    });
    builder.inline(button);
    var childContext = {
      name: id,
      className: 'highlightable ' + id,
      referenceHovers: context.referenceHovers || []
    };
    selected.forEach(function (child) { processExplanation(child, builder, childContext); });
  }

  function renderTrailer(node, builder, context) {
    var anchor = elt('button', 'explanation-trailer');
    anchor.type = 'button';
    var inner = new Builder(context.className);
    processExplanation(node.value, inner, context);
    appendInlineFragment(anchor, inner.fragment);
    anchor.setAttribute('aria-expanded', node.expanded ? 'true' : 'false');
    anchor.addEventListener('click', function (event) {
      event.stopPropagation();
      node.expanded = !node.expanded;
      renderDocumentPane();
    });
    builder.inline(anchor);
    if (node.expanded) processExplanation(node.trailer, builder, context);
  }

  function appendLeanEvidenceField(parent, label, value) {
    if (value == null || value === '') return;
    var field = elt('div', 'lean-evidence-field');
    if (label !== '') {
      var heading = elt('div', 'lean-evidence-field-label');
      heading.appendChild(text(label));
      field.appendChild(heading);
    }
    var body = elt('pre', 'lean-evidence-code');
    body.appendChild(text(String(value)));
    field.appendChild(body);
    parent.appendChild(field);
  }

  function appendLeanGoal(parent, goal) {
    if (!goal) return;
    var section = elt('section', 'lean-evidence-goal');
    var heading = elt('div', 'lean-evidence-section-title');
    heading.appendChild(text('Goal state'));
    section.appendChild(heading);
    var items = elt('div', 'goal-items');
    appendContextItems(items, goal.items || []);
    section.appendChild(items);
    var target = elt('div', 'goal-context-target');
    target.appendChild(text((goal.targetPrefix || 'Goal:') + ' '));
    target.appendChild(richText(goal.target || ''));
    section.appendChild(target);
    parent.appendChild(section);
  }

  function renderLeanEvidence(node, builder, context) {
    processExplanation(node.value, builder, context);
    var button = elt('button', 'lean-evidence-button');
    button.type = 'button';
    button.textContent = '⊢';
    button.title = node.expanded
      ? 'Hide the exact formalization' : 'Show the exact formalization';
    button.setAttribute('aria-expanded', node.expanded ? 'true' : 'false');
    button.setAttribute('aria-label', node.expanded
      ? 'Hide the exact Lean formalization' : 'Show the exact Lean formalization');
    button.addEventListener('click', function (event) {
      event.stopPropagation();
      node.expanded = !node.expanded;
      renderDocumentPane();
    });
    builder.inline(text(' '));
    builder.inline(button);
    if (!node.expanded) return;

    var panel = elt('aside', 'lean-evidence-panel');
    panel.setAttribute('aria-label', 'Exact Lean formalization');
    appendLeanGoal(panel, node.goalState);
    (node.evidence || []).forEach(function (evidence, index) {
      var entry = elt('section', 'lean-evidence-entry');
      var heading = elt('div', 'lean-evidence-summary');
      var declaration = elt('code', 'lean-evidence-declaration');
      declaration.appendChild(text(evidence.declaration || evidence.label || ('evidence ' + index)));
      heading.appendChild(declaration);
      entry.appendChild(heading);
      if (evidence.source) {
        var source = elt('div', 'lean-evidence-source');
        source.appendChild(text(
          evidence.source.module + ':' + evidence.source.line + ':' + evidence.source.column
        ));
        entry.appendChild(source);
      }
      appendLeanEvidenceField(entry, 'Formal statement', evidence.expected || evidence.type);
      if (!evidence.expected || evidence.type !== evidence.expected) {
        appendLeanEvidenceField(entry, 'Checked type', evidence.type);
      }
      var proof = elt('details', 'lean-evidence-proof');
      var proofSummary = elt('summary', 'lean-evidence-proof-summary');
      proofSummary.appendChild(text('Proof term'));
      proof.appendChild(proofSummary);
      appendLeanEvidenceField(proof, '', evidence.term);
      entry.appendChild(proof);
      panel.appendChild(entry);
    });
    builder.block(panel);
  }

  function renderConcreteProof(node, builder, context) {
    var button = elt('button', 'concrete-proof-button');
    button.type = 'button';
    button.textContent = '⋯';
    button.setAttribute('aria-expanded', node.expanded ? 'true' : 'false');
    button.setAttribute('aria-label', node.expanded
      ? 'Hide the complete proof tree' : 'Show the complete proof tree');
    button.title = node.expanded
      ? 'Hide the complete proof tree' : 'Show the complete proof tree';
    button.addEventListener('click', function (event) {
      event.stopPropagation();
      node.expanded = !node.expanded;
      renderDocumentPane();
    });
    builder.inline(button);
    processExplanation(node.expanded ? node.proof : node.value, builder, context);
  }

  function renderList(node, builder, context, ordered) {
    var list = elt(ordered ? 'ol' : 'ul', 'explanation-list');
    (node.value || []).forEach(function (item, index) {
      var li = elt('li');
      var child = new Builder(context.className);
      processExplanation(item, child, {
        name: context.name + '-item-' + index,
        className: context.className,
        referenceHovers: context.referenceHovers || []
      });
      li.appendChild(child.fragment);
      list.appendChild(li);
    });
    builder.block(list);
  }

  function renderComputation(node, builder, context) {
    var table = elt('table', 'explanation-computation');
    var first = true;
    (node.steps || []).forEach(function (step, index) {
      var row = elt('tr');
      var lhs = elt('td', 'computation-lhs');
      if (first) typeset(lhs, node.start || '', false, context.referenceHovers || []);
      var rel = elt('td', 'computation-rel');
      typeset(rel, step.rel || '', false, context.referenceHovers || []);
      var rhs = elt('td', 'computation-rhs');
      typeset(rhs, step.rhs || '', false, context.referenceHovers || []);
      var reason = elt('td', 'computation-explanation');
      var child = new Builder(context.className);
      processExplanation(step.expl, child, {
        name: context.name + '-computation-' + index,
        className: context.className,
        referenceHovers: context.referenceHovers || []
      });
      reason.appendChild(child.fragment);
      row.appendChild(lhs); row.appendChild(rel); row.appendChild(rhs); row.appendChild(reason);
      table.appendChild(row);
      first = false;
    });
    if (!(node.steps || []).length) {
      var row = elt('tr'); var cell = elt('td');
      typeset(cell, node.start || '', false, context.referenceHovers || []);
      row.appendChild(cell); table.appendChild(row);
    }
    builder.block(table);
  }

  function processExplanation(node, builder, context) {
    if (!node) return;
    switch (node.type) {
      case 'Explanation.empty': return;
      case 'Explanation.paragraphBreak': builder.breakParagraph(); return;
      case 'Explanation.str':
        builder.inline(richText(node.value, context.referenceHovers || [])); return;
      case 'Explanation.human': {
        var human = elt('span', 'human');
        human.appendChild(richText(node.value, context.referenceHovers || []));
        builder.inline(human); return;
      }
      case 'Explanation.join':
        (node.value || []).forEach(function (child) { processExplanation(child, builder, context); });
        return;
      case 'Explanation.goalState': renderGoalButton(node.goalState, builder); return;
      case 'Explanation.withReplacement': renderReplacement(node, builder, context); return;
      case 'Explanation.withTrailer': renderTrailer(node, builder, context); return;
      case 'Explanation.withToolTip': renderTooltip(node, builder, context); return;
      case 'Explanation.withLeanHovers':
        processExplanation(node.value, builder, {
          name: context.name,
          className: context.className,
          referenceHovers: mergedReferenceHovers(node.hovers, context.referenceHovers)
        }); return;
      case 'Explanation.withLeanEvidence': renderLeanEvidence(node, builder, context); return;
      case 'Explanation.withConcreteProof': renderConcreteProof(node, builder, context); return;
      case 'Explanation.indent': {
        var indented = elt('div', 'explanation-indent');
        var childBuilder = new Builder(context.className);
        processExplanation(node.value, childBuilder, context);
        indented.appendChild(childBuilder.fragment);
        builder.block(indented); return;
      }
      case 'Explanation.list': renderList(node, builder, context, false); return;
      case 'Explanation.enumList': renderList(node, builder, context, true); return;
      case 'Explanation.computation': renderComputation(node, builder, context); return;
      default: throw new Error('Unknown explanation type ' + node.type);
    }
  }

  function setAllExpanded(state, node) {
    if (!node) return;
    switch (node.type) {
      case 'LemmaInfo':
        setAllExpanded(state, node.statementExplanation);
        (node.explanations || []).forEach(function (x) { setAllExpanded(state, x); }); return;
      case 'Explanation.join':
      case 'Explanation.list':
      case 'Explanation.enumList':
        (node.value || []).forEach(function (x) { setAllExpanded(state, x); }); return;
      case 'Explanation.withReplacement':
        node.expanded = state;
        ['preValue', 'value', 'postValue', 'preReplace', 'replace', 'postReplace']
          .forEach(function (field) { setAllExpanded(state, node[field]); });
        return;
      case 'Explanation.withTrailer':
        node.expanded = state; setAllExpanded(state, node.value); setAllExpanded(state, node.trailer); return;
      case 'Explanation.withToolTip':
      case 'Explanation.withLeanHovers':
      case 'Explanation.indent': setAllExpanded(state, node.value); return;
      case 'Explanation.withLeanEvidence':
        // Exact Lean inspection is an independent tier.  Global semantic
        // expansion never opens or closes it.
        setAllExpanded(state, node.value); return;
      case 'Explanation.withConcreteProof':
        // The complete Lean tree is an independent inspection tier.  The
        // global controls expand only the explanation currently on display;
        // switching tiers remains the explicit job of the ellipsis button.
        setAllExpanded(state, node.expanded ? node.proof : node.value);
        return;
      case 'Explanation.computation':
        (node.steps || []).forEach(function (step) { setAllExpanded(state, step.expl); }); return;
      default: return;
    }
  }

  function setGlobalExpansion(state, node) {
    if (!node) return;
    switch (node.type) {
      case 'LemmaInfo':
        setGlobalExpansion(state, node.statementExplanation);
        (node.explanations || []).forEach(function (x) { setGlobalExpansion(state, x); }); return;
      case 'Explanation.join':
      case 'Explanation.list':
      case 'Explanation.enumList':
        (node.value || []).forEach(function (x) { setGlobalExpansion(state, x); }); return;
      case 'Explanation.withReplacement':
        node.expanded = state;
        ['preValue', 'value', 'postValue', 'preReplace', 'replace', 'postReplace']
          .forEach(function (field) { setGlobalExpansion(state, node[field]); });
        return;
      case 'Explanation.withTrailer':
        node.expanded = state;
        setGlobalExpansion(state, node.value);
        setGlobalExpansion(state, node.trailer); return;
      case 'Explanation.withToolTip':
      case 'Explanation.withLeanHovers':
      case 'Explanation.indent': setGlobalExpansion(state, node.value); return;
      case 'Explanation.withLeanEvidence':
        setGlobalExpansion(state, node.value); return;
      case 'Explanation.withConcreteProof':
        node.expanded = state;
        if (state) {
          setGlobalExpansion(true, node.proof);
        } else {
          setGlobalExpansion(false, node.value);
          setGlobalExpansion(false, node.proof);
        }
        return;
      case 'Explanation.computation':
        (node.steps || []).forEach(function (step) {
          setGlobalExpansion(state, step.expl);
        }); return;
      default: return;
    }
  }

  function expandableCount(node) {
    if (!node) return 0;
    switch (node.type) {
      case 'LemmaInfo':
        return expandableCount(node.statementExplanation) +
          (node.explanations || []).reduce(function (n, child) {
          return n + expandableCount(child);
        }, 0);
      case 'Explanation.join':
      case 'Explanation.list':
      case 'Explanation.enumList':
        return (node.value || []).reduce(function (n, child) {
          return n + expandableCount(child);
        }, 0);
      case 'Explanation.withReplacement':
        return 1 + ['preValue', 'value', 'postValue', 'preReplace', 'replace', 'postReplace']
          .reduce(function (n, field) { return n + expandableCount(node[field]); }, 0);
      case 'Explanation.withTrailer':
        return 1 + expandableCount(node.value) + expandableCount(node.trailer);
      case 'Explanation.withToolTip':
      case 'Explanation.withLeanHovers':
      case 'Explanation.indent':
        return expandableCount(node.value);
      case 'Explanation.withLeanEvidence':
        return expandableCount(node.value);
      case 'Explanation.withConcreteProof':
        return expandableCount(node.expanded ? node.proof : node.value);
      case 'Explanation.computation':
        return (node.steps || []).reduce(function (n, step) {
          return n + expandableCount(step.expl);
        }, 0);
      default:
        return 0;
    }
  }

  function containsGoalState(node) {
    if (!node) return false;
    if (Array.isArray(node)) return node.some(containsGoalState);
    if (typeof node !== 'object') return false;
    if (node.type === 'Explanation.goalState') return true;
    return Object.keys(node).some(function (key) {
      return key !== 'goalState' && containsGoalState(node[key]);
    });
  }

  function theoremNode(decl, index) {
    var theorem = elt('section', 'theorem');
    var statement = elt('div', 'theorem-statement authored-text');
    var heading = elt('p', 'theorem-heading');
    var name = elt('span', 'theorem-name');
    var headingText = decl.header || 'Theorem';
    if (decl.title) headingText += ' (' + decl.title + ')';
    name.appendChild(text(headingText + '.'));
    // A paper theorem does not print its fully-qualified Lean declaration
    // name as part of the prose. Keep the exact identifier available without
    // letting it determine line width or visual hierarchy.
    name.title = decl.name || '';
    if (decl.declarationHover) attachLeanHover(name, decl.declarationHover);
    heading.appendChild(name);
    statement.appendChild(heading);
    if (decl.statementExplanation) {
      var statementBuilder = new Builder('highlightable theorem-statement-content');
      processExplanation(decl.statementExplanation, statementBuilder, {
        name: 'theorem-' + index + '-statement',
        className: 'highlightable theorem-statement-content',
        referenceHovers: []
      });
      statement.appendChild(statementBuilder.fragment);
    } else {
      heading.appendChild(text(' '));
      heading.appendChild(richText(decl.statement || ''));
    }
    theorem.appendChild(statement);

    (decl.explanations || []).forEach(function (explanation, proofIndex) {
      var proof = elt('div', 'proof authored-text');
      var builder = new Builder('highlightable');
      processExplanation(explanation, builder, {
        name: 'theorem-' + index + '-proof-' + proofIndex,
        className: 'highlightable',
        referenceHovers: []
      });
      proof.appendChild(builder.fragment);
      var paragraphs = proof.querySelectorAll('p');
      if (!paragraphs.length) {
        var p = elt('p'); proof.appendChild(p); paragraphs = [p];
      }
      var prefix = elt('span', 'proof-text'); prefix.appendChild(text('Proof. '));
      paragraphs[0].insertBefore(prefix, paragraphs[0].firstChild);
      var qed = elt('span', 'qed'); qed.appendChild(text('□'));
      paragraphs[paragraphs.length - 1].appendChild(qed);
      theorem.appendChild(proof);
    });
    return theorem;
  }

  var docPane;
  var goalPane;
  var gutterPane;

  function renderDocumentPane() {
    if (!docPane) return;
    clearFloatingTooltips();
    docPane.replaceChildren();
    serial = 0;
    renderedGoals = [];
    var documentNode = elt('div', 'document');
    var disclosureCount = declarations.reduce(function (n, decl) {
      return n + expandableCount(decl);
    }, 0);
    var controls = null;
    if (disclosureCount > 0) {
      controls = elt('div', 'proof-controls');
      function action(label, state) {
        var button = elt('input'); button.type = 'button'; button.value = label;
        button.addEventListener('click', function () {
          declarations.forEach(function (decl) { setGlobalExpansion(state, decl); });
          highlightAfterRender = null; renderDocumentPane();
        });
        return button;
      }
      controls.appendChild(action('Expand all', true));
      controls.appendChild(action('Collapse all', false));
    }
    declarations.forEach(function (decl, index) {
      if (decl.type !== 'LemmaInfo') throw new Error('Unknown declaration type ' + decl.type);
      documentNode.appendChild(theoremNode(decl, index));
    });
    if (controls) documentNode.appendChild(controls);
    docPane.appendChild(documentNode);
    // An expanded subproof may own a more specific proof-state marker.  Once
    // that branch is collapsed, do not leave a stale state selected with no
    // corresponding active marker in the document.
    if (currentGoal && renderedGoals.indexOf(currentGoal) < 0) {
      currentGoal = null;
      renderGoalPane();
    }
    if (highlightAfterRender) {
      var highlighted = docPane.querySelectorAll('.' + highlightAfterRender);
      highlighted.forEach(function (node) { node.classList.add('highlight'); });
      window.setTimeout(function () {
        highlighted.forEach(function (node) { node.classList.remove('highlight'); });
      }, 850);
      highlightAfterRender = null;
    }
  }

  function commaSeparated(items) {
    if (!items.length) return '';
    if (items.length === 1) return items[0];
    if (items.length === 2) return items[0] + ' and ' + items[1];
    return items.slice(0, -1).join(', ') + ' and ' + items[items.length - 1];
  }

  function mergeableContextItem(item) {
    return item.name != null && item.pluralType != null && !item.auxDecl &&
      !item.implDetail && !item.implementationDetail && item.value == null;
  }

  // A proof-state pane should expose the mathematical context, not names
  // manufactured by Lean's elaborator. Ordinary binder names such as X, q,
  // or f remain useful; anonymous, hygienic, and fully-qualified names do not.
  function publicContextName(name) {
    if (name == null) return null;
    var value = String(name);
    if (!value || value[0] === '_' || value.indexOf('✝') >= 0 ||
        value.indexOf('_' + 'uniq') >= 0 || value.indexOf('_' + 'hyg') >= 0 ||
        value.indexOf('.') >= 0 || /^inst[A-Z0-9_]/.test(value)) return null;
    return value;
  }

  function appendContextGroup(parent, group) {
    var first = group[0];
    var line = elt('div', 'goal-context-item');
    if (first.auxDecl) line.classList.add('goal-context-item-aux-decl');
    if (first.implDetail || first.implementationDetail) {
      line.classList.add('goal-context-item-implementation-detail');
    }
    if (group.every(function (item) { return !item.used; })) {
      line.classList.add('goal-context-item-unused');
    }
    var description = elt('div', 'goal-context-item-text');
    var names = group.map(function (item) { return publicContextName(item.name); })
      .filter(function (name) { return name != null; })
      .map(function (name) { return '\\(' + name + '\\)'; });
    var typeText = group.length === 1 ? first.singularType : first.pluralType;
    var valueText = first.value == null ? '' : ' := \\(' + first.value + '\\)';
    description.appendChild(richText(
      (names.length ? commaSeparated(names) + ' ' : '') + (typeText || '') + valueText
    ));
    line.appendChild(description);
    parent.appendChild(line);
  }

  function appendContextItems(parent, sourceItems) {
    var current = [];
    function flush() {
      if (current.length) appendContextGroup(parent, current);
      current = [];
    }
    (sourceItems || []).forEach(function (item) {
      if (current.length && mergeableContextItem(item) &&
          mergeableContextItem(current[0]) &&
          item.singularType === current[0].singularType) {
        current.push(item);
      } else {
        flush();
        current.push(item);
        if (!mergeableContextItem(item)) flush();
      }
    });
    flush();
  }

  function renderGoalPane() {
    if (!goalPane) return;
    goalPane.replaceChildren();
    if (!currentGoal) {
      goalPane.hidden = true;
      if (gutterPane) gutterPane.hidden = true;
      if (docPane) docPane.style.flexBasis = '100%';
      return;
    }
    goalPane.hidden = false;
    if (gutterPane) gutterPane.hidden = false;
    if (docPane) docPane.style.flexBasis = '75%';
    goalPane.style.flexBasis = '25%';
    var view = elt('div', 'goal-view');
    var header = elt('div', 'goal-header'); header.appendChild(text('Current proof state:'));
    view.appendChild(header);
    var items = elt('div', 'goal-items');
    appendContextItems(items, currentGoal.items || []);
    view.appendChild(items);
    var target = elt('div', 'goal-context-target');
    target.appendChild(text((currentGoal.targetPrefix || 'Goal:') + ' '));
    target.appendChild(richText(currentGoal.target || ''));
    view.appendChild(target);
    if (currentGoal.paragraphForm && currentGoal.paragraphForm !== currentGoal.target) {
      var paragraph = elt('p', 'goal-paragraph-form');
      paragraph.appendChild(richText(currentGoal.paragraphForm));
      view.appendChild(paragraph);
    }
    goalPane.appendChild(view);
  }

  function installResize(gutter, left, right) {
    var dragging = false;
    gutter.addEventListener('pointerdown', function (event) {
      dragging = true; gutter.setPointerCapture(event.pointerId); event.preventDefault();
    });
    gutter.addEventListener('pointermove', function (event) {
      if (!dragging) return;
      var box = mountNode.getBoundingClientRect();
      var pct = Math.max(20, Math.min(80, (event.clientX - box.left) / box.width * 100));
      left.style.flexBasis = pct + '%'; right.style.flexBasis = (100 - pct) + '%';
      repositionActiveTooltip();
    });
    gutter.addEventListener('pointerup', function () { dragging = false; });
    gutter.addEventListener('pointercancel', function () { dragging = false; });
  }

  function mount() {
    var root = elt('div', 'main-div');
    var hasGoals = containsGoalState(declarations);
    docPane = elt('div', 'main-doc');
    docPane.addEventListener('scroll', repositionActiveTooltip, { passive: true });
    window.addEventListener('resize', repositionActiveTooltip);
    if (!hasGoals) {
      root.classList.add('main-div-no-goals');
      docPane.style.flexBasis = '100%';
      root.appendChild(docPane);
      mountNode.replaceChildren(root);
      renderDocumentPane();
      return;
    }
    docPane.style.flexBasis = '75%';
    gutterPane = elt('div', 'gutter gutter-horizontal');
    gutterPane.setAttribute('role', 'separator');
    gutterPane.setAttribute('aria-orientation', 'vertical');
    goalPane = elt('aside', 'main-goal');
    goalPane.id = 'proof-state-pane';
    goalPane.setAttribute('aria-label', 'Proof state inspector');
    goalPane.style.flexBasis = '25%';
    root.appendChild(docPane); root.appendChild(gutterPane); root.appendChild(goalPane);
    mountNode.replaceChildren(root);
    installResize(gutterPane, docPane, goalPane);
    renderDocumentPane(); renderGoalPane();
  }

  // Small test surface: it exposes state-changing behavior, never raw HTML.
  var api = {
    expandAll: function () { declarations.forEach(function (x) { setGlobalExpansion(true, x); }); renderDocumentPane(); },
    collapseAll: function () { declarations.forEach(function (x) { setGlobalExpansion(false, x); }); renderDocumentPane(); },
    contextNameForDisplay: publicContextName,
    hasGoalPane: function () { return !!goalPane; },
    visibleGoalCount: function () { return renderedGoals.length; },
    declarations: declarations
  };

  mount();
  return api;
  }

  var publicApi = window.InformalizationMM || {};
  publicApi.mount = mountInformalization;

  function installLocalLiveReload() {
    if (window.__informalizationLiveReloadInstalled) return;
    if (window.location.protocol !== 'http:' && window.location.protocol !== 'https:') return;
    if (window.location.hostname !== '127.0.0.1' &&
        window.location.hostname !== 'localhost' &&
        window.location.hostname !== '::1') return;
    window.__informalizationLiveReloadInstalled = true;

    var stampUrl = new URL('.informalization-build-stamp', window.location.href);
    var lastStamp = null;
    window.setInterval(function () {
      fetch(stampUrl.href + '?t=' + Date.now(), { cache: 'no-store' })
        .then(function (response) {
          if (!response.ok) throw new Error('no live build stamp');
          return response.text();
        })
        .then(function (stamp) {
          stamp = stamp.trim();
          if (!stamp) return;
          if (lastStamp !== null && stamp !== lastStamp) window.location.reload();
          lastStamp = stamp;
        })
        .catch(function () {
          // Static readers intentionally have no live-build stamp.
        });
    }, 1000);
  }

  var dataNode = document.getElementById('informalization-data');
  var mountNode = document.getElementById('main');
  if (dataNode && mountNode) {
    try {
      var declarations = JSON.parse(dataNode.textContent);
      var standaloneApi = mountInformalization(mountNode, declarations);
      if (standaloneApi) Object.keys(standaloneApi).forEach(function (key) {
        publicApi[key] = standaloneApi[key];
      });
    } catch (_err) {
      mountNode.appendChild(document.createTextNode('Could not parse explanation data.'));
    }
  }
  window.InformalizationMM = publicApi;
  installLocalLiveReload();
})();
