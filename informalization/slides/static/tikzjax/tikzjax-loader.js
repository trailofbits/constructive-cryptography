/* Experimental TikZJax loader for the draft deck.

   As of 2026-08-18 the public v1 bundle is available, but that bundle asks for
   its hashed WASM and core files below /v1/, where the CDN returns 403.  The
   assets are still available at the site root.  We patch only those two URLs,
   then execute the upstream bundle unchanged.

   This intentionally remains an experiment: it needs a network connection and
   TikZJax still emits SVG. */
(async () => {
  const bundleUrl = "https://tikzjax.com/v1/tikzjax.js";
  const wasmName = "3f69afb974a1e83f66a36f7618f88a38c254034b.wasm";
  const coreName = "b565ab0b474e8e557d954694b7379a57db669ac9.gz";

  try {
    const response = await fetch(bundleUrl);
    if (!response.ok) {
      throw new Error(`TikZJax bundle request failed: ${response.status}`);
    }

    let source = await response.text();
    source = source
      .replace(`s+"/${wasmName}"`, `"https://tikzjax.com/${wasmName}"`)
      .replace(`s+"/${coreName}"`, `"https://tikzjax.com/${coreName}"`);

    const objectUrl = URL.createObjectURL(
      new Blob([source], { type: "text/javascript" })
    );
    const script = document.createElement("script");
    script.src = objectUrl;
    script.addEventListener("load", () => {
      URL.revokeObjectURL(objectUrl);
      // The upstream bundle assigns window.onload.  If its asynchronous load
      // completed after the page load event, invoke that handler explicitly.
      if (document.readyState === "complete" && typeof window.onload === "function") {
        window.onload();
      }
    }, { once: true });
    document.head.appendChild(script);
  } catch (error) {
    document.documentElement.dataset.tikzjaxError = String(error);
    console.error(error);
  }
})();
