import VersoManual

open Lean
open Verso Doc Elab Genre.Manual
open Verso.ArgParse
open Verso.Code.External
open SubVerso.Module

namespace VersoTools

private def parseDeclNames (code : StrLit) : Array Name :=
  code.getString.splitOn "\n"
    |> List.toArray
    |> .map (fun s => String.trimAscii s |>.copy)
    |> .filter (not ∘ String.isEmpty)
    |> .map String.toName

private def findDeclItems (items : Array ModuleItem) (declName : Name) : Array ModuleItem :=
  let declName := declName.eraseMacroScopes
  items.filter fun item =>
    item.defines.any fun n => n.eraseMacroScopes == declName

@[code_block_expander leanDecl]
def leanDecl : CodeBlockExpander
  | args, code => do
    let cfg : CodeModuleContext ← parseThe CodeModuleContext args
    let { module := moduleName, project, showProofStates := _, defSite := _ } := cfg
    let declNames := parseDeclNames code
    if declNames.isEmpty then
      throwErrorAt code "Expected at least one declaration name"
    let items ← loadModuleContent project moduleName.getId.toString
    let mut blocks := #[]
    for declName in declNames do
      let found := findDeclItems items declName
      if found.isEmpty then
        throwErrorAt code
          m!"Declaration '{declName}' not found in module '{moduleName.getId}'."
      if found.size = 1 then
        let some item := found[0]?
          | throwErrorAt code m!"Internal error while extracting '{declName}'."
        blocks := blocks.push <| ← ``(
          Verso.Code.External.ExternalCode.leanBlock
            (genre := Verso.Genre.Manual)
            $(quote item.code)
            $(quote cfg.toCodeConfig))
      else
        throwErrorAt code
          m!"Declaration '{declName}' was found in multiple command items in module '{moduleName.getId}'."
    pure blocks

end VersoTools
