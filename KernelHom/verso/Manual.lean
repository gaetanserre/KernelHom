/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
    {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
    {{<link rel="stylesheet" href="static/style.css"/>}},
    {{<script src="static/scripts.js"></script>}},
]

def git := "https://github.com/gaetanserre/KernelHom"

def config : RenderConfig := {
  extraHead := extraHead,
  sourceLink := some git,
  issueLink := some (git ++ "/issues"),
}

def main := manualMain (%doc Manual.Front) (config := config)
