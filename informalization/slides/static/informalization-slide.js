(function () {
  'use strict';

  function proofParagraphContaining(container, marker) {
    if (!container) return null;
    return Array.prototype.find.call(
      container.querySelectorAll('p.highlightable'),
      function (paragraph) {
        return (paragraph.textContent || '').indexOf(marker) !== -1;
      }
    ) || null;
  }

  function markProofMilestone(element, order) {
    if (!element) return;
    element.classList.add('proof-milestone');
    element.dataset.proofMilestone = String(order);
  }

  function visibleProofMilestone(host) {
    var order = 1;
    host.querySelectorAll('.proof-milestone-step.visible').forEach(
      function (step) {
        var stepOrder = Number(step.dataset.proofMilestoneStep);
        if (Number.isFinite(stepOrder)) order = Math.max(order, stepOrder);
      }
    );
    return order;
  }

  function centerProofMilestone(host, target, behavior) {
    var pane = host.querySelector('.main-doc');
    if (!pane || !target) return;

    window.requestAnimationFrame(function () {
      var paneRect = pane.getBoundingClientRect();
      var targetRect = target.getBoundingClientRect();
      var scale = pane.clientHeight > 0
        ? paneRect.height / pane.clientHeight
        : 1;
      var targetCenter = targetRect.top + targetRect.height / 2;
      var paneCenter = paneRect.top + paneRect.height / 2;
      var nextTop = pane.scrollTop + (targetCenter - paneCenter) / scale;
      var maximumTop = Math.max(0, pane.scrollHeight - pane.clientHeight);
      pane.scrollTo({
        top: Math.max(0, Math.min(maximumTop, nextTop)),
        behavior: behavior
      });
    });
  }

  function activateProofMilestone(host, order, behavior) {
    var target = null;
    host.querySelectorAll('.proof-milestone').forEach(function (milestone) {
      var active = milestone.dataset.proofMilestone === String(order);
      milestone.classList.toggle('is-active', active);
      if (active) target = milestone;
    });
    host.dataset.activeProofMilestone = String(order);
    centerProofMilestone(host, target, behavior);
  }

  function milestonesEnabled(host) {
    return host.dataset.informalizationMilestones !== 'false';
  }

  function syncProofMilestone(host, behavior) {
    if (!milestonesEnabled(host)) return;
    activateProofMilestone(host, visibleProofMilestone(host), behavior);
  }

  function markProofMilestones(host) {
    var theorem = host.querySelector('.theorem');
    if (!theorem) return;

    var statement = theorem.querySelector(
      ':scope > .theorem-statement.authored-text'
    );
    var proof = theorem.querySelector(':scope > .proof.authored-text');
    var restriction = proofParagraphContaining(
      proof,
      'The total-block restriction permits'
    );
    var conditional = proofParagraphContaining(proof, 'Following CR18');
    var collision = proofParagraphContaining(proof, 'In a blind strategy');
    var conditionalDisplays = conditional
      ? conditional.querySelectorAll('.math-display')
      : [];

    markProofMilestone(statement && statement.querySelector('.math-display'), 1);
    markProofMilestone(restriction && restriction.querySelector('.math-display'), 2);
    markProofMilestone(conditionalDisplays[1], 3);
    markProofMilestone(conditionalDisplays[2], 4);
    markProofMilestone(collision && collision.querySelector('.math-display'), 5);
    syncProofMilestone(host, 'auto');
  }

  function mountReader(host) {
    if (host.dataset.informalizationMounted === 'true') return;
    var mountNode = host.querySelector('[data-informalization-mount]');
    // A bare view shares the document embedded by the main proof slide.
    var dataNode = host.querySelector('[data-informalization-data]') ||
      document.querySelector('[data-informalization-data]');
    if (!mountNode || !dataNode) {
      host.dataset.informalizationError = 'missing-reader-markup';
      return;
    }
    if (!window.InformalizationMM ||
        typeof window.InformalizationMM.mount !== 'function') {
      retryReaderRuntime(host);
      return;
    }

    try {
      delete host.dataset.informalizationError;
      delete host.dataset.informalizationRuntimeRetries;
      var declarations = JSON.parse(dataNode.textContent);
      var tooltipRoot = document.createElement('div');
      tooltipRoot.className = 'informalization-native-host informalization-tooltip-portal';
      document.body.appendChild(tooltipRoot);
      var reader = window.InformalizationMM.mount(mountNode, declarations, {
        tooltipRoot: tooltipRoot,
        sectionTag: 'article'
      });
      host.__informalizationReader = reader;
      host.dataset.informalizationMounted = 'true';
      if (milestonesEnabled(host)) markProofMilestones(host);
    } catch (error) {
      host.dataset.informalizationError = 'invalid-document';
      mountNode.textContent = 'Could not load the informalization.';
      window.console.error(error);
    }
  }

  function retryReaderRuntime(host) {
    if (host.dataset.informalizationRuntimeRetryScheduled === 'true') return;
    var retries = Number(host.dataset.informalizationRuntimeRetries || 0);
    if (retries >= 60) {
      host.dataset.informalizationError = 'missing-reader-runtime';
      return;
    }
    host.dataset.informalizationRuntimeRetries = String(retries + 1);
    host.dataset.informalizationRuntimeRetryScheduled = 'true';
    window.setTimeout(function () {
      delete host.dataset.informalizationRuntimeRetryScheduled;
      scheduleReader(host);
    }, 50);
  }

  function waitForPresentSlide(host) {
    var slide = host.closest('section');
    if (!slide || slide.classList.contains('present')) return true;
    if (host.__informalizationPresentObserver) return false;

    var observer = new MutationObserver(function () {
      if (!slide.classList.contains('present')) return;
      observer.disconnect();
      delete host.__informalizationPresentObserver;
      delete host.dataset.informalizationWaitingForPresent;
      scheduleReader(host);
    });
    host.__informalizationPresentObserver = observer;
    host.dataset.informalizationWaitingForPresent = 'true';
    observer.observe(slide, { attributes: true, attributeFilter: ['class'] });
    return false;
  }

  function mountAll() {
    document.querySelectorAll('[data-informalization-reader]').forEach(mountReader);
  }

  function readerInSlide(slide) {
    if (!slide || typeof slide.querySelector !== 'function') return null;
    return slide.querySelector('[data-informalization-reader]');
  }

  function currentReader() {
    return readerInSlide(
      document.querySelector('.reveal .slides section.present')
    );
  }

  function scheduleReader(host) {
    if (!host || host.dataset.informalizationMounted === 'true' ||
        host.dataset.informalizationMountScheduled === 'true') return;
    host.dataset.informalizationMountScheduled = 'true';

    function commitMount() {
      delete host.dataset.informalizationMountScheduled;
      if (!waitForPresentSlide(host)) return;
      mountReader(host);
    }

    // Let Reveal establish and paint the current slide before constructing the
    // proof reader.  This avoids doing the full proof render in the initial
    // DOMContentLoaded task or against a still-hidden slide canvas.
    window.requestAnimationFrame(function () {
      window.requestAnimationFrame(function () {
        if (typeof window.requestIdleCallback === 'function') {
          window.requestIdleCallback(commitMount, { timeout: 120 });
        } else {
          window.setTimeout(commitMount, 0);
        }
      });
    });
  }

  function mountCurrent(event) {
    var host = readerInSlide(event && event.currentSlide) || currentReader();
    if (host && host.dataset.informalizationMounted === 'true') {
      syncProofMilestone(host, 'auto');
    } else {
      scheduleReader(host);
    }
  }

  function fragmentChanged(event) {
    var slide = event && event.fragment
      ? event.fragment.closest('section')
      : null;
    var host = readerInSlide(slide) || currentReader();
    if (!host) return;
    if (host.dataset.informalizationMounted === 'true') {
      syncProofMilestone(host, 'smooth');
    } else {
      scheduleReader(host);
    }
  }

  function bindRevealLifecycle() {
    if (!window.Reveal || typeof window.Reveal.on !== 'function') return false;
    window.Reveal.on('ready', mountCurrent);
    window.Reveal.on('slidechanged', mountCurrent);
    window.Reveal.on('fragmentshown', fragmentChanged);
    window.Reveal.on('fragmenthidden', fragmentChanged);
    if (typeof window.Reveal.isReady === 'function' && window.Reveal.isReady()) {
      mountCurrent({ currentSlide: window.Reveal.getCurrentSlide() });
    }
    return true;
  }

  window.InformalizationSlide = {
    mountAll: mountAll,
    mountCurrent: mountCurrent
  };

  if (!bindRevealLifecycle()) {
    var bindAfterLoad = function () {
      if (!bindRevealLifecycle()) mountAll();
    };
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', bindAfterLoad, { once: true });
    } else {
      bindAfterLoad();
    }
  }
})();
