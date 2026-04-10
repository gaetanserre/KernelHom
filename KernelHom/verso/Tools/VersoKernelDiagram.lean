import KernelHom.Tactic.Hom.KernelDiagram
import Lean.PrettyPrinter.Delaborator.SubExpr
import VersoManual

open Lean Meta Elab Command PrettyPrinter Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr
open CategoryTheory
open Verso Doc Elab Genre.Manual
open Verso.ArgParse
open Mathlib.Tactic.Widget
open Verso.Genre.Manual.InlineLean.Scopes
open MonoidalCategory ComonObj

namespace VersoTools

/--
Pretty-print `MonoidalCategoryStruct.tensorObj` using `⊗` inside string diagram labels.

The upstream widget labels are generated with `Widget.ppExprTagged`, so this delaborator affects the
label payload before it is serialized to HTML/JSON for the local Verso bridge.
-/
@[app_delab CategoryTheory.MonoidalCategoryStruct.tensorObj]
meta def delabTensorObj : Delab :=
  whenNotPPOption getPPExplicit <|
  whenPPOption getPPNotation <|
  withOverApp 5 do
    let x ← withNaryArg 3 delab
    let y ← withNaryArg 4 delab
    let stx ← `(($x ⊗ $y))
    annotateTermInfo stx

structure StringDiagramPayload where
  html : Json
  diagramHash : Nat
  interactiveCodeHash : Nat
  deriving ToJson, FromJson, Quote

private def stringDiagramCss : CSS := .mk <| "
:root {
  --vscode-editor-foreground: var(--verso-text-color, #111);
  --vscode-editor-background: #fff;
  --vscode-editorHoverWidget-background: #fff;
  --vscode-editorHoverWidget-foreground: var(--verso-text-color, #111);
  --vscode-editorHoverWidget-border: #98B2C0;
}

.verso-string-diagram {
  margin: 1rem 0;
  color: var(--verso-text-color, #111);
}

.verso-string-diagram-root {
  overflow-x: auto;
}

.verso-string-diagram .sd-loading {
  color: var(--verso-fg-secondary, #666);
  font-style: italic;
}

.verso-string-diagram .sd-inline-code {
  font-family: var(--verso-font-mono, monospace);
  font-size: 0.85rem;
  line-height: 1.3;
  white-space: pre-wrap;
  color: var(--verso-code-color, #111);
  background: transparent;
}

.verso-string-diagram .relative { position: relative; }
.verso-string-diagram .absolute { position: absolute; }
.verso-string-diagram .dib { display: inline-block; }
.verso-string-diagram .flex { display: flex; gap: 1rem; flex-wrap: nowrap; align-items:" ++
"flex-start; }
.verso-string-diagram .w-50 { flex: 1 1 0; min-width: 0; }

@media (max-width: 900px) {
  .verso-string-diagram .flex { flex-wrap: wrap; }
  .verso-string-diagram .w-50 { flex-basis: 24rem; }
}
.verso-string-diagram .top-0 { top: 0; }
.verso-string-diagram .right-0 { right: 0; }
.verso-string-diagram .pv1 { padding-top: 0.25rem; padding-bottom: 0.25rem; }
.verso-string-diagram .ph2 { padding-left: 0.5rem; padding-right: 0.5rem; }
.verso-string-diagram .mv2 { margin-top: 0.5rem; margin-bottom: 0.5rem; }
.verso-string-diagram .pointer { cursor: pointer; }
.verso-string-diagram .link { text-decoration: none; }
.verso-string-diagram .dim { opacity: 0.85; }
.verso-string-diagram .dim:hover { opacity: 1; }
.verso-string-diagram .o-30 { opacity: 0.3; }
.verso-string-diagram .red { color: #b00020; }
"

private def stringDiagramLoaderJs : JsFile where
  filename := "string-diagram/string-diagram-loader.js"
  defer := true
  contents := .mk <| include_str "Assets" / "string-diagram-loader.js"
  sourceMap? := none

private def stringDiagramWidgetJs : DataFile where
  filename := "string-diagram/string-diagram-widget.js"
  contents := (include_str "Assets" / "string-diagram-widget.js").toUTF8

block_extension Block.stringDiagramWidget (payload : StringDiagramPayload) where
  data := ToJson.toJson payload
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let payload ←
        match FromJson.fromJson? (α := StringDiagramPayload) data with
        | .ok payload => pure payload
        | .error err =>
          Verso.Doc.Html.HtmlT.logError s!"Could not deserialize string diagram payload: {err}"
          pure {
            html := Json.null,
            diagramHash := 0,
            interactiveCodeHash := 0
          }
      let htmlJson := Json.compress payload.html
      pure {{
        <div class="verso-string-diagram">
          <div class="verso-string-diagram-root"
               "data-html"={{htmlJson}}
               "data-diagram-hash"={{toString payload.diagramHash}}
               "data-interactive-code-hash"={{toString payload.interactiveCodeHash}}>
            <div class="sd-loading">"Loading string diagram..."</div>
          </div>
        </div>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ _ _ _ _ => pure .empty
  extraCss := [stringDiagramCss]
  extraJsFiles := ({ } : Std.HashSet JsFile).insert stringDiagramLoaderJs
  extraDataFiles := ({ } : Std.HashSet DataFile).insert stringDiagramWidgetJs

private def diagramHash : Nat :=
  (hash ProofWidgets.Penrose.Diagram.javascript).toNat

private def interactiveCodeHash : Nat :=
  (hash ProofWidgets.InteractiveCode.javascript).toNat

private def parseTermSyntax (str : StrLit) : DocElabM (TSyntax `term) := do
  let input := str.getString
  match Parser.runParserCategory (← getEnv) `term input (← getFileName) with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwErrorAt str err

private def mkKernelDiagramPayload (stx : TSyntax `term) : DocElabM StringDiagramPayload := do
  let e ← liftM <| (do
    let e ← try
      mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo stx)
    catch _ =>
      runWithOpenDecls <| runWithVariables fun _ => do
        let e ← Term.elabTerm stx none
        let e ← instantiateMVars e
        Term.levelMVarToParam e
    pure e : TermElabM Expr)
  let some html ← liftM <| (do
    let html ← KernelDiagram.kernelMorOrEqM? e
    pure html : TermElabM (Option ProofWidgets.Html))
    | throwErrorAt stx "could not find a morphism or equality for a string diagram"
  let html := (Lean.Server.RpcEncodable.rpcEncode html).run {} |>.1
  pure {
    html := html,
    diagramHash := diagramHash,
    interactiveCodeHash := interactiveCodeHash
  }

/--
Render a string diagram in generated HTML documentation using the upstream proofwidgets
HTML/Penrose pipeline. The input must be a Lean term or declaration whose type is a morphism or an
equality of morphisms.
-/
@[code_block_expander kernelDiagram]
def kernelDiagram : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.run (α := Unit) .done args
    let stx ← parseTermSyntax str
    let payload ← mkKernelDiagramPayload stx
    pure #[← ``(Verso.Doc.Block.other (Block.stringDiagramWidget $(quote payload)) #[])]

end VersoTools
