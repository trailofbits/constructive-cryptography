/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.

Build target for the Swiss Crypto Day deck.
-/
import VersoSlides
import VersoUtil.BinFiles
import DraftTalk

open VersoSlides
open Verso.BinFiles

private def presentationCss : CssFile := {
  filename := "custom-draft-base-v2.css"
  contents := ⟨include_str "static/custom.css"⟩
}

private def tangerineCss : CssFile := {
  filename := "tob-tangerine.css"
  contents := ⟨include_str "static/tob-tangerine.css"⟩
}

private def draftCss : CssFile := {
  filename := "draft-talk-v18.css"
  contents := ⟨include_str "static/draft-talk.css"⟩
}

private def tikzCbcCss : CssFile := {
  filename := "tikz-cbc-v3.css"
  contents := ⟨include_str "static/tikz-cbc.css"⟩
}

private def informalizationNativeCss : CssFile := {
  filename := "informalization-native-v1.css"
  contents := ⟨include_str "static/informalization-native.css"⟩
}

private def jsonForScriptData (json : String) : String :=
  (json.replace "&" "\\u0026").replace "<" "\\u003c" |>.replace ">" "\\u003e"

private def tangerineDraftTheme : CustomTheme where
  stylesheet := presentationCss
  assets :=
    ThemeAsset.fromDir (include_bin_dir "static/fonts") ++
    ThemeAsset.fromDir (include_bin_dir "static/images") ++
    #[{
      filename := "tikzjax-loader.js"
      contents := include_bin "static/tikzjax/tikzjax-loader.js"
    }]
  highlightTheme := .github

def main : IO UInt32 := do
  let config : Config := {
    theme := .custom tangerineDraftTheme
    center := false
    width := 1600
    height := 900
    margin := 0.025
    slideNumber := true
    transition := "none"
    outputDir := "_draft_talk"
    extraCss := #[tangerineCss, draftCss, tikzCbcCss, informalizationNativeCss]
    extraJs := #["tikzjax-loader.js", "massot-miller.js", "informalization-slide.js"]
  }
  let rc ← slidesMain (config := config) (doc := %doc DraftTalk)

  -- Read TikZ at execution time rather than compile time. Editing a `.tex`
  -- file therefore requires only rerunning the deck generator, not touching a
  -- Lean source file to invalidate Lake's incremental build cache.
  let primitive ← IO.FS.readFile "tikz/cbc-primitive.tex"
  let converter ← IO.FS.readFile "tikz/cbc-converter.tex"
  let comparison ← IO.FS.readFile "tikz/cbc-comparison.tex"
  -- Lake does not track `include_str` dependencies. Refresh the authored CSS
  -- at execution time too, so a geometry-scale edit needs no version bump.
  let tikzCssSource ← IO.FS.readFile "static/tikz-cbc.css"
  IO.FS.writeFile (config.outputDir / tikzCbcCss.filename) tikzCssSource

  -- The native slide consumes the same public document and renderer as the
  -- standalone reader. Keep the deck build separate from theorem extraction
  -- so visual work remains possible while the downstream proof evolves.
  let informalizationPath := "../preview/cbc-mac.document.json"
  let informalization ← IO.FS.readFile informalizationPath
  unless informalization.contains "CBC-MAC Randomness Expansion" do
    throw <| IO.userError s!"{informalizationPath} is not the CBC informalization"
  unless informalization.contains "Explanation.withReplacement" do
    throw <| IO.userError s!"{informalizationPath} is not an interactive Explanation document"

  let deckTheme ← IO.FS.readFile "static/tob-tangerine.css"
  if deckTheme.contains ".reveal .controls" then
    throw <| IO.userError "the deck theme captures the informalization reader's proof controls"

  let readerJs ← IO.FS.readFile "../web/massot-miller.js"
  unless readerJs.contains "publicApi.mount = mountInformalization" do
    throw <| IO.userError "the shared informalization renderer does not expose its mount contract"
  let slideJs ← IO.FS.readFile "static/informalization-slide.js"
  unless slideJs.contains "window.InformalizationMM.mount" do
    throw <| IO.userError "the Verso adapter does not use the shared informalization mount contract"
  if slideJs.contains "controlsPlacement" then
    throw <| IO.userError "the Verso adapter overrides the informalization reader's control placement"
  let readerCss ← IO.FS.readFile "../web/massot-miller.css"
  let nativeCssTemplate ← IO.FS.readFile "static/informalization-native.css"
  let cssMarker := "/* @@MASSOT_MILLER_CSS@@ */"
  unless nativeCssTemplate.contains cssMarker do
    throw <| IO.userError "the native informalization stylesheet lost its shared-style marker"
  let scopedReaderCss := readerCss.replace ":root {" ":scope {"
  let nativeCss := nativeCssTemplate.replace cssMarker scopedReaderCss
  unless nativeCss.contains "@scope (.informalization-native-host)" &&
      nativeCss.contains ".proof-controls" &&
      !nativeCss.contains cssMarker do
    throw <| IO.userError "the native reader styles were not scoped into the Verso host"
  if nativeCss.contains ".controls-viewport" || nativeCss.contains "padding-bottom: 3rem;" then
    throw <| IO.userError "the Verso host overrides the reader's native scrolling controls"
  unless nativeCss.contains "background: #fff !important;" do
    throw <| IO.userError "the Verso reader lost its continuous slide canvas"
  IO.FS.writeFile (config.outputDir / "massot-miller.js") readerJs
  IO.FS.writeFile (config.outputDir / "informalization-slide.js") slideJs
  IO.FS.writeFile (config.outputDir / informalizationNativeCss.filename) nativeCss

  let htmlPath := config.outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html
    |>.replace cbcPrimitiveTikzToken primitive
    |>.replace cbcConverterTikzToken converter
    |>.replace cbcComparisonTikzToken comparison
    |>.replace cbcInformalizationDataToken (jsonForScriptData informalization)
  unless html.contains "data-informalization-reader=\"true\"" do
    throw <| IO.userError "the CBC slide did not render its native informalization host"
  if html.contains cbcInformalizationDataToken then
    throw <| IO.userError "the CBC informalization document was not embedded"
  if html.contains "<iframe" || html.contains "background-iframe" ||
      html.contains "current-informalization.html" then
    throw <| IO.userError "the CBC slide regressed to iframe embedding"
  IO.FS.writeFile htmlPath html
  let obsoleteReaderPage := config.outputDir / "current-informalization.html"
  if ← obsoleteReaderPage.pathExists then IO.FS.removeFile obsoleteReaderPage
  return rc
