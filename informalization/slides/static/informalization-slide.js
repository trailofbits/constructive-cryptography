(function () {
  'use strict';

  function mountReader(host) {
    if (host.dataset.informalizationMounted === 'true') return;
    var mountNode = host.querySelector('[data-informalization-mount]');
    var dataNode = host.querySelector('[data-informalization-data]');
    if (!mountNode || !dataNode || !window.InformalizationMM ||
        typeof window.InformalizationMM.mount !== 'function') {
      host.dataset.informalizationError = 'missing-reader-runtime';
      return;
    }

    try {
      var declarations = JSON.parse(dataNode.textContent);
      var tooltipRoot = document.createElement('div');
      tooltipRoot.className = 'informalization-native-host informalization-tooltip-portal';
      document.body.appendChild(tooltipRoot);
      var reader = window.InformalizationMM.mount(mountNode, declarations, {
        tooltipRoot: tooltipRoot
      });
      host.__informalizationReader = reader;
      host.dataset.informalizationMounted = 'true';
    } catch (error) {
      host.dataset.informalizationError = 'invalid-document';
      mountNode.textContent = 'Could not load the informalization.';
      window.console.error(error);
    }
  }

  function mountAll() {
    document.querySelectorAll('[data-informalization-reader]').forEach(mountReader);
  }

  window.InformalizationSlide = { mountAll: mountAll };
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', mountAll, { once: true });
  } else {
    mountAll();
  }
})();
