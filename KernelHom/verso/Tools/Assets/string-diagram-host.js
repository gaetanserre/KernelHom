import * as React from "react";
import { createRoot } from "react-dom/client";
import HtmlDisplay from "proofwidgets-html-display";
import Diagram from "proofwidgets-penrose-display";
import {
  EnvPosContext,
  InteractiveCode,
  registerWidgetModule,
} from "proofwidgets-infoview-shim";

function ensureModules(host) {
  registerWidgetModule(host.dataset.diagramHash, { default: Diagram });
  registerWidgetModule(host.dataset.interactiveCodeHash, { default: InteractiveCode });
}

function mountStringDiagram(host) {
  if (host.dataset.stringDiagramMounted === "true") {
    return;
  }
  ensureModules(host);
  const html = JSON.parse(host.dataset.html);
  const root = createRoot(host);
  root.render(
    React.createElement(
      EnvPosContext.Provider,
      { value: { line: 0, character: 0 } },
      React.createElement(HtmlDisplay, { html }),
    ),
  );
  host.dataset.stringDiagramMounted = "true";
}

function mountAllStringDiagrams() {
  document
    .querySelectorAll(".verso-string-diagram-root[data-html]")
    .forEach((host) => {
      try {
        mountStringDiagram(host);
      } catch (error) {
        host.textContent = error instanceof Error ? error.message : String(error);
        host.classList.add("red");
      }
    });
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", mountAllStringDiagrams, { once: true });
} else {
  mountAllStringDiagrams();
}

window.StringDiagramWidget = { mountAllStringDiagrams };