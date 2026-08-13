import VersoManual
import Textbook.Bibliography

open Lean
open Verso Doc Elab ArgParse

namespace Textbook

private def textbookBlockCss := r#"
.textbook-block {
  margin: var(--verso--box-vertical-margin) 0;
  border: 1px solid color-mix(in srgb, currentColor 32%, transparent);
  border-radius: 0.45rem;
  overflow: hidden;
  background: color-mix(in srgb, currentColor 2.5%, transparent);
}

.textbook-block-title {
  padding: 0.65rem var(--verso--box-padding);
  border-bottom: 1px solid color-mix(in srgb, currentColor 24%, transparent);
  background: color-mix(in srgb, currentColor 7%, transparent);
  font-family: var(--verso-structure-font-family);
  font-weight: 700;
}

.textbook-block-body {
  padding: 0.2rem var(--verso--box-padding) var(--verso--box-padding);
}

.textbook-block-body > code.hl.lean.block {
  display: block;
  box-sizing: border-box;
  margin: 1rem 0;
  padding: 0.8rem 1rem;
  border: 1px solid color-mix(in srgb, currentColor 24%, transparent);
  border-radius: 0.35rem;
  background: color-mix(in srgb, currentColor 6%, transparent);
  box-shadow: inset 0 1px 2px color-mix(in srgb, currentColor 8%, transparent);
  overflow-x: auto;
}

.textbook-definition {
  border-color: color-mix(in srgb, #2563eb 55%, currentColor);
}

.textbook-definition > .textbook-block-title {
  background: color-mix(in srgb, #2563eb 12%, transparent);
}

.textbook-theorem {
  border-color: color-mix(in srgb, #7c3aed 55%, currentColor);
}

.textbook-theorem > .textbook-block-title {
  background: color-mix(in srgb, #7c3aed 12%, transparent);
}
"#

private def textbookDetailsCss := r#"
.textbook-details {
  margin: var(--verso--box-vertical-margin) 0;
  border: 1px solid color-mix(in srgb, currentColor 22%, transparent);
  border-radius: 0.4rem;
  background: color-mix(in srgb, currentColor 2.5%, transparent);
  overflow: hidden;
}

.textbook-details > summary {
  padding: 0.65rem var(--verso--box-padding);
  background: color-mix(in srgb, currentColor 6%, transparent);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
}

.textbook-details[open] > summary {
  border-bottom: 1px solid color-mix(in srgb, currentColor 18%, transparent);
}

.textbook-details-body {
  padding: 0.2rem var(--verso--box-padding) var(--verso--box-padding);
}

.textbook-details-body > code.hl.lean.block {
  display: block;
  box-sizing: border-box;
  margin: 1rem 0;
  padding: 0.8rem 1rem;
  border: 1px solid color-mix(in srgb, currentColor 24%, transparent);
  border-radius: 0.35rem;
  background: color-mix(in srgb, currentColor 6%, transparent);
  overflow-x: auto;
}
"#

structure TitledBlockConfig where
  title : StrLit

instance : FromArgs TitledBlockConfig DocElabM where
  fromArgs := TitledBlockConfig.mk <$> .positional `title .strLit

block_extension Block.theoremBlock (title : String) where
  data := title
  traverse _ _ _ := pure none
  toTeX := some fun _ go _ _ contents => contents.mapM go
  toHtml := some fun _ go _ data contents => open Verso.Output.Html in do
    let .str title := data
      | reportError "Invalid theorem title"
        return .empty
    pure {{
      <section class="textbook-block textbook-theorem">
        <div class="textbook-block-title">{{s!"Theorem: {title}"}}</div>
        <div class="textbook-block-body">{{← contents.mapM go}}</div>
      </section>
    }}
  extraCss := [textbookBlockCss]

block_extension Block.definitionBlock (title : String) where
  data := title
  traverse _ _ _ := pure none
  toTeX := some fun _ go _ _ contents => contents.mapM go
  toHtml := some fun _ go _ data contents => open Verso.Output.Html in do
    let .str title := data
      | reportError "Invalid definition title"
        return .empty
    pure {{
      <section class="textbook-block textbook-definition">
        <div class="textbook-block-title">{{s!"Definition: {title}"}}</div>
        <div class="textbook-block-body">{{← contents.mapM go}}</div>
      </section>
    }}
  extraCss := [textbookBlockCss]

block_extension Block.detailsBlock (title : String) where
  data := title
  traverse _ _ _ := pure none
  toTeX := some fun _ go _ _ contents => contents.mapM go
  toHtml := some fun _ go _ data contents => open Verso.Output.Html in do
    let .str title := data
      | reportError "Invalid details title"
        return .empty
    pure {{
      <details class="textbook-details">
        <summary>{{title}}</summary>
        <div class="textbook-details-body">{{← contents.mapM go}}</div>
      </details>
    }}
  extraCss := [textbookDetailsCss]

@[directive]
meta def «theorem» : DirectiveExpanderOf TitledBlockConfig
  | {title}, contents => do
    let contents ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.theoremBlock $(quote title.getString)) #[$contents,*])

@[directive]
meta def definition : DirectiveExpanderOf TitledBlockConfig
  | {title}, contents => do
    let contents ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.definitionBlock $(quote title.getString)) #[$contents,*])

@[directive]
meta def details : DirectiveExpanderOf TitledBlockConfig
  | {title}, contents => do
    let contents ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.detailsBlock $(quote title.getString)) #[$contents,*])

set_option quotPrecheck false in
/-- Elaborate Lean code and render its actual output directly below the code block. -/
@[code_block]
meta def leanEval :
    CodeBlockExpanderOf Verso.Genre.Manual.InlineLean.LeanBlockConfig
  | config, source => do
    let outputName ← mkFreshUserName `_textbookLeanOutput
    let config := { config with name := some outputName }
    let code ← Verso.Genre.Manual.InlineLean.lean config source
    let messages ← Verso.Genre.Manual.InlineLean.getOutputs (mkIdent outputName)
    let outputs ← messages.toArray.mapM fun message =>
      ``(Verso.Doc.Block.other
          { Verso.Genre.Manual.InlineLean.Block.leanOutput with
            data := ToJson.toJson
              ($(quote message), false, ([] : List Name)) }
          #[])
    let blocks := #[code] ++ outputs
    ``(Verso.Doc.Block.concat #[$blocks,*])

end Textbook
