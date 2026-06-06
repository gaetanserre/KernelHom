(function () {
  const key = "__stringDiagramWidgetModulePromise";
  if (window[key]) {
    return;
  }
  const script = document.currentScript;
  if (!script || !script.src) {
    return;
  }
  const suffix = "string-diagram-loader.js";
  const base = script.src.endsWith(suffix) ? script.src.slice(0, -suffix.length) : script.src;
  window[key] = import(base + "string-diagram-widget.js").catch((error) => {
    console.error("Failed to load string diagram widget module", error);
    throw error;
  });
})();