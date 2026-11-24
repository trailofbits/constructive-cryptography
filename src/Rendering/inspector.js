// Shared by the Lean component and standalone exports. No term-derived JavaScript is evaluated.
// The infoview can load the same module concurrently under distinct blob URLs.
// Coordinate per document so those independent instances still share a single pin.
const inspectorStateKey = Symbol.for('CCWidget.inspectorState');
const inspectorState = document[inspectorStateKey] ??= {active: null, changing: false};

export function attachInspector(button, popup) {
  let pinned = false, keyboard = false, restoringFocus = false, timer;
  let overButton = false, overPopup = false;
  const listeners = [];
  const listen = (target, event, handler, options) => {
    target.addEventListener(event, handler, options);
    listeners.push(() => target.removeEventListener(event, handler, options));
  };
  const cancel = () => clearTimeout(timer);
  const isOpen = () => popup.matches(':popover-open');
  const ownsFocus = () => button === document.activeElement || popup.contains(document.activeElement);
  const sync = () => {
    button.setAttribute('aria-expanded', String(isOpen()));
    button.setAttribute('aria-pressed', String(pinned && isOpen()));
    button.title = pinned ? 'Pinned; double-click to unpin, or click outside to close' :
      'Hover to inspect; double-click or press Enter to pin';
    popup.dataset.pinned = String(pinned && isOpen());
  };
  const place = () => {
    if (!isOpen()) return;
    const r = button.getBoundingClientRect();
    const below = Math.max(0, innerHeight - r.bottom - 16);
    const above = Math.max(0, r.top - 16);
    const needed = popup.scrollHeight + popup.offsetHeight - popup.clientHeight;
    const down = below >= needed || below >= above;
    // Keep the trigger reachable for the second click, even when source text is expanded.
    popup.style.maxHeight = (down ? below : above) + 'px';
    popup.style.right = 'auto'; popup.style.bottom = 'auto';
    popup.style.left = Math.max(8, Math.min(r.left, innerWidth - popup.offsetWidth - 8)) + 'px';
    popup.style.top = Math.max(8, down ? r.bottom + 8 : r.top - popup.offsetHeight - 8) + 'px';
  };
  const hide = (restore = false) => {
    cancel(); pinned = false; keyboard = false; restoringFocus = true;
    if (inspectorState.active?.popup === popup) inspectorState.active = null;
    if (!inspectorState.changing && isOpen()) {
      inspectorState.changing = true;
      try { popup.hidePopover(); } finally { inspectorState.changing = false; }
    }
    if (restore) button.focus({preventScroll:true});
    queueMicrotask(() => { restoringFocus = false; });
    sync();
  };
  const show = (intent = 'hover') => {
    if (inspectorState.changing || restoringFocus || !popup.isConnected) return;
    if (inspectorState.active && inspectorState.active.popup !== popup) {
      if (intent === 'hover' && inspectorState.active.isPinned()) return;
      inspectorState.active.hide();
    }
    cancel(); inspectorState.changing = true;
    try { if (!isOpen()) popup.showPopover(); } finally { inspectorState.changing = false; }
    inspectorState.active = {popup, hide, isPinned:() => pinned};
    sync(); place();
  };
  const leave = () => {
    cancel();
    if (!pinned) timer = setTimeout(() => {
      if (!pinned && !overButton && !overPopup &&
          !(keyboard && ownsFocus())) hide();
    }, 160);
  };
  const togglePin = () => { show('activate'); pinned = !pinned; sync(); leave(); };
  const keyDown = event => {
    keyboard = true;
    if (event.key === 'Escape') {
      event.preventDefault(); event.stopPropagation(); hide(true);
    }
  };
  listen(button, 'pointerenter', event => {
    if (event.pointerType !== 'touch') { overButton = true; keyboard = false; show(); }
  });
  listen(button, 'pointerleave', () => { overButton = false; keyboard = false; leave(); });
  listen(button, 'focus', () => {
    if (!restoringFocus && button.matches(':focus-visible')) { keyboard = true; show('focus'); }
  });
  listen(button, 'blur', leave);
  listen(button, 'click', event => {
    if (event.detail === 0) togglePin(); // Keyboard equivalent of a pointer double-click.
    else { keyboard = false; show('activate'); }
  });
  listen(button, 'dblclick', event => { event.preventDefault(); togglePin(); });
  listen(button, 'keydown', keyDown);
  listen(popup, 'pointerenter', () => { overPopup = true; cancel(); });
  listen(popup, 'pointerleave', () => { overPopup = false; keyboard = false; leave(); });
  listen(popup, 'focusin', cancel);
  listen(popup, 'focusout', leave);
  listen(popup, 'keydown', keyDown);
  listen(popup.querySelector('.cc-inspector-close'), 'click', () => hide(true));
  listen(document, 'pointerdown', event => {
    if (inspectorState.active?.popup !== popup) return;
    keyboard = false;
    if (!button.contains(event.target) && !popup.contains(event.target)) hide();
  }, true);
  listen(document, 'pointermove', () => {
    if (inspectorState.active?.popup === popup && keyboard) { keyboard = false; leave(); }
  });
  // Chromium can retain :hover on the last element inside an iframe after pointer exit.
  listen(document, 'pointerout', event => {
    if (!event.relatedTarget) { overButton = false; overPopup = false; keyboard = false; leave(); }
  });
  // Clicking the editor, outside the infoview iframe, also dismisses the inspector.
  listen(window, 'blur', () => hide());
  listen(window, 'resize', place);
  listen(window, 'scroll', place, true);
  listen(popup, 'toggle', () => {
    if (!isOpen()) {
      pinned = false; keyboard = false; cancel();
      if (inspectorState.active?.popup === popup) inspectorState.active = null;
    }
    sync(); place();
  });
  const observer = new ResizeObserver(place);
  observer.observe(popup);
  sync();
  return () => { hide(); observer.disconnect(); listeners.forEach(remove => remove()); };
}

// Without scripting the exported details remain accessible.
export function enhanceExportedInspectors() {
  if (!('showPopover' in HTMLElement.prototype)) return;
  document.querySelectorAll('.cc-inspector-static').forEach((details, index) => {
    const summary = details.querySelector(':scope > summary');
    const popup = details.querySelector(':scope > .cc-inspector-body');
    const holder = document.createElement('span');
    holder.className = 'cc-inspector cc-inspector-export';
    const button = document.createElement('button');
    button.type = 'button'; button.className = 'cc-inspector-trigger';
    button.textContent = summary.textContent;
    const label = summary.getAttribute('aria-label');
    button.setAttribute('aria-label', label); button.setAttribute('aria-haspopup', 'dialog');
    popup.id = 'cc-export-inspector-' + index;
    button.setAttribute('aria-controls', popup.id);
    popup.setAttribute('popover', 'auto'); popup.setAttribute('role', 'dialog');
    popup.setAttribute('aria-label', label);
    const close = document.createElement('button');
    close.type = 'button'; close.className = 'cc-inspector-close'; close.textContent = '×';
    close.setAttribute('aria-label', 'Close information');
    popup.prepend(close); holder.append(button, popup); details.replaceWith(holder);
    attachInspector(button, popup);
  });
}
