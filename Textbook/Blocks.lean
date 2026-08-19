import VersoManual
import Textbook.Bibliography

open Lean
open Verso Doc Elab ArgParse

namespace Textbook

private def textbookLeanCss := r#"
/* Give every elaborated Lean 4 block the same container, whether it appears
   on its own or inside one of the textbook's semantic blocks. */
code.hl.lean.block {
  display: block;
  box-sizing: border-box;
  margin: 1rem 0;
  padding: 0.8rem 1rem;
  border: 1px solid color-mix(in srgb, currentColor 24%, transparent);
  border-radius: 0.35rem;
  background: color-mix(in srgb, currentColor 6%, transparent);
  box-shadow: inset 0 1px 2px color-mix(in srgb, currentColor 8%, transparent);
  overflow-x: auto;

  /* Verso emits semantic classes for elaborated Lean tokens. */
  --verso-code-keyword-color: #6d28d9;
  --verso-code-const-color: #0369a1;
  --verso-code-var-color: #9a3412;
}

code.hl.lean.block .sort {
  color: #be123c;
}

code.hl.lean.block .literal.string,
code.hl.lean.block .literal.char {
  color: #047857;
}

code.hl.lean.block .literal.number {
  color: #b45309;
}

code.hl.lean.block .comment {
  color: #64748b;
  font-style: italic;
}
"#

private def textbookThemeCss := r#"
.header-title-wrapper {
  min-width: 0;
}

.header-title {
  overflow: hidden;
  text-overflow: ellipsis;
}

.textbook-theme-toggle {
  position: fixed;
  right: 1rem;
  bottom: 1rem;
  z-index: 1000;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  min-height: 2.5rem;
  padding: 0.55rem 0.8rem;
  border: 1px solid color-mix(in srgb, currentColor 30%, transparent);
  border-radius: 999px;
  background: #fff;
  color: inherit;
  box-shadow: 0 2px 8px color-mix(in srgb, #000 24%, transparent);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-size: 0.9rem;
  font-weight: 600;
  line-height: 1;
}

.textbook-theme-toggle:hover {
  background: color-mix(in srgb, currentColor 14%, transparent);
}

.textbook-theme-toggle:focus-visible {
  outline: 2px solid #2563eb;
  outline-offset: 2px;
}

html[data-textbook-theme="dark"] {
  color-scheme: dark;
  --verso-text-color: #e5e7eb;
  --verso-code-color: #e5e7eb;
  --verso-structure-color: #f8fafc;
  --verso-background-color: #0f172a;
  --verso-surface-color: #111827;
  --verso-border-color: #374151;
  --verso-link-color: #7dd3fc;
  --verso-link-visited-color: #c4b5fd;
  --verso-muted-color: #94a3b8;
  --verso-selected-color: #334155;
  --verso-toc-background-color: #111827;
  --verso-toc-text-color: #e5e7eb;
  --verso-toc-border-color: #374151;
  --verso-toc-resize-handle-color: #94a3b8;
  --verso-burger-toc-visible-color: #e5e7eb;
  --verso-burger-toc-visible-shadow-color: #111827;
  --verso-burger-toc-hidden-color: #e5e7eb;
  --verso-burger-toc-hidden-shadow-color: #111827;
}

html[data-textbook-theme="dark"] body {
  background: #0f172a;
  color: var(--verso-text-color);
}

html[data-textbook-theme="dark"] header {
  background: #111827;
  box-shadow: 0 0 6px #020617;
}

html[data-textbook-theme="dark"] .textbook-theme-toggle {
  background: #1e293b;
  border-color: #475569;
  color: #f8fafc;
}

html[data-textbook-theme="dark"] .header-title,
html[data-textbook-theme="dark"] .prev-next-buttons > *,
html[data-textbook-theme="dark"] #toc a {
  color: #e5e7eb;
}

html[data-textbook-theme="dark"] #toc a:hover {
  color: #fff;
}

html[data-textbook-theme="dark"] #toc .split-toc label.toggle-split-toc::before {
  background-color: #e5e7eb;
}

/* Verso's search UI is loaded after the page, so style both its header
   combobox and its full search page explicitly. */
html[data-textbook-theme="dark"] #search-wrapper .combobox .cb_edit,
html[data-textbook-theme="dark"] #search-wrapper ul[role="listbox"],
html[data-textbook-theme="dark"] .search-page-input {
  background-color: #111827;
  border-color: #475569;
  color: #f8fafc;
}

html[data-textbook-theme="dark"] #search-wrapper .cb_edit:empty::before,
html[data-textbook-theme="dark"] .search-page-input::placeholder {
  color: #94a3b8;
}

html[data-textbook-theme="dark"] #search-wrapper .combobox .group.focus .cb_edit,
html[data-textbook-theme="dark"] #search-wrapper .combobox .group .cb_edit:hover,
html[data-textbook-theme="dark"] #search-wrapper [role="listbox"].focus li[aria-selected="true"],
html[data-textbook-theme="dark"] #search-wrapper .search-result:hover,
html[data-textbook-theme="dark"] .search-page-list li.search-result:hover,
html[data-textbook-theme="dark"] .search-page-list li.search-result:focus-within {
  background-color: #334155;
}

html[data-textbook-theme="dark"] main p a,
html[data-textbook-theme="dark"] main li a,
html[data-textbook-theme="dark"] main dt a,
html[data-textbook-theme="dark"] main dd a {
  color: #7dd3fc;
}

html[data-textbook-theme="dark"] main p a:visited,
html[data-textbook-theme="dark"] main li a:visited,
html[data-textbook-theme="dark"] main dt a:visited,
html[data-textbook-theme="dark"] main dd a:visited {
  color: #c4b5fd;
}

html[data-textbook-theme="dark"] code.hl.lean.block {
  --verso-code-keyword-color: #c4b5fd;
  --verso-code-const-color: #7dd3fc;
  --verso-code-var-color: #fdba74;
}

html[data-textbook-theme="dark"] code.hl.lean.block .sort {
  color: #fda4af;
}

html[data-textbook-theme="dark"] code.hl.lean.block .literal.string,
html[data-textbook-theme="dark"] code.hl.lean.block .literal.char {
  color: #6ee7b7;
}

html[data-textbook-theme="dark"] code.hl.lean.block .literal.number {
  color: #fcd34d;
}

html[data-textbook-theme="dark"] code.hl.lean.block .comment {
  color: #94a3b8;
}

@media (hover: hover) {
  html[data-textbook-theme="dark"] .hl.lean .token.binding-hl,
  html[data-textbook-theme="dark"] .hl.lean .literal:hover,
  html[data-textbook-theme="dark"] .hl.lean .token.typed:hover,
  html[data-textbook-theme="dark"] .hl.lean .tactic:has(> .tactic-toggle:not(:checked)) > label:hover:not(:has(.tactic > label:hover)) {
    background-color: #293548;
  }

  html[data-textbook-theme="dark"] .hl.lean .has-info.information:hover {
    background-color: #243b5a;
  }

  html[data-textbook-theme="dark"] .hl.lean .has-info.warning:hover {
    background-color: #44351f;
  }

  html[data-textbook-theme="dark"] .hl.lean .has-info.error:hover {
    background-color: #4a2930;
  }
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="lean"],
html[data-textbook-theme="dark"] .tippy-box[data-theme~="message"],
html[data-textbook-theme="dark"] .tippy-box[data-theme~="tactic"] {
  background-color: #1e293b;
  border-color: #475569;
  color: #cbd5e1;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="warning"] {
  border-color: #a16207;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="error"] {
  border-color: #b91c1c;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="info"] {
  border-color: #2563eb;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="lean"][data-placement^="top"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="message"][data-placement^="top"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="tactic"][data-placement^="top"] > .tippy-arrow::before {
  border-top-color: #1e293b;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="lean"][data-placement^="bottom"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="message"][data-placement^="bottom"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="tactic"][data-placement^="bottom"] > .tippy-arrow::before {
  border-bottom-color: #1e293b;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="lean"][data-placement^="left"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="message"][data-placement^="left"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="tactic"][data-placement^="left"] > .tippy-arrow::before {
  border-left-color: #1e293b;
}

html[data-textbook-theme="dark"] .tippy-box[data-theme~="lean"][data-placement^="right"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="message"][data-placement^="right"] > .tippy-arrow::before,
html[data-textbook-theme="dark"] .tippy-box[data-theme~="tactic"][data-placement^="right"] > .tippy-arrow::before {
  border-right-color: #1e293b;
}

html[data-textbook-theme="dark"] .tippy-box .hl.lean .hover-info code,
html[data-textbook-theme="dark"] .tippy-box .hl.lean code,
html[data-textbook-theme="dark"] .tippy-box .hl.lean .verso-message {
  color: #cbd5e1;
}

html[data-textbook-theme="dark"] .hl.lean .tactic-state,
html[data-textbook-theme="dark"] .hl.lean.popup .tactic-state {
  background-color: #172033;
  border-color: #475569;
  color: #cbd5e1;
}

html[data-textbook-theme="dark"] .hl.lean .hover-info .sep {
  border-top-color: #475569;
}
"#

private def textbookThemeJs := r#"
(function () {
  const storageKey = "textbook-theme";
  const root = document.documentElement;
  let savedTheme = null;

  try {
    savedTheme = localStorage.getItem(storageKey);
  } catch (_) {
    // Continue with the reader's operating-system preference.
  }

  const systemTheme = window.matchMedia?.("(prefers-color-scheme: dark)").matches
    ? "dark"
    : "light";
  root.dataset.textbookTheme = savedTheme === "dark" || savedTheme === "light"
    ? savedTheme
    : systemTheme;

  document.addEventListener("DOMContentLoaded", () => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "textbook-theme-toggle";

    const updateButton = () => {
      const isDark = root.dataset.textbookTheme === "dark";
      button.textContent = isDark ? "☀ Light mode" : "☾ Dark mode";
      button.setAttribute("aria-label", isDark
        ? "Switch to light mode"
        : "Switch to dark mode");
      button.title = button.getAttribute("aria-label");
      button.setAttribute("aria-pressed", String(isDark));
    };

    button.addEventListener("click", () => {
      root.dataset.textbookTheme = root.dataset.textbookTheme === "dark"
        ? "light"
        : "dark";
      try {
        localStorage.setItem(storageKey, root.dataset.textbookTheme);
      } catch (_) {
        // The toggle still works for this page if storage is unavailable.
      }
      updateButton();
    });

    updateButton();
    document.body.appendChild(button);
  });
})();
"#

private def textbookBlockCss := r#"
.textbook-block {
  margin: var(--verso--box-vertical-margin) 0;
  border: 1px solid color-mix(in srgb, currentColor 32%, transparent);
  border-radius: 0.45rem;
  /* Verso's margin notes float outside the text column. Clipping here makes
     notes inside a definition or theorem disappear on wide screens. */
  overflow: visible;
  background: color-mix(in srgb, currentColor 2.5%, transparent);
}

.textbook-block-title {
  padding: 0.65rem var(--verso--box-padding);
  border-bottom: 1px solid color-mix(in srgb, currentColor 24%, transparent);
  border-radius: calc(0.45rem - 1px) calc(0.45rem - 1px) 0 0;
  background: color-mix(in srgb, currentColor 7%, transparent);
  font-family: var(--verso-structure-font-family);
  font-weight: 700;
}

.textbook-block-body {
  padding: 0.2rem var(--verso--box-padding) var(--verso--box-padding);
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
  /* Keep margin notes in expanded details visible outside the box. */
  overflow: visible;
}

.textbook-details > summary {
  padding: 0.65rem var(--verso--box-padding);
  border-radius: calc(0.4rem - 1px);
  background: color-mix(in srgb, currentColor 6%, transparent);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
}

.textbook-details[open] > summary {
  border-bottom: 1px solid color-mix(in srgb, currentColor 18%, transparent);
  border-radius: calc(0.4rem - 1px) calc(0.4rem - 1px) 0 0;
}

.textbook-details-body {
  padding: 0.2rem var(--verso--box-padding) var(--verso--box-padding);
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
  extraCss := [textbookLeanCss, textbookThemeCss, textbookBlockCss]
  extraJs := { Verso.Genre.Manual.JS.mk textbookThemeJs }

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
  extraCss := [textbookLeanCss, textbookThemeCss, textbookBlockCss]
  extraJs := { Verso.Genre.Manual.JS.mk textbookThemeJs }

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
  extraCss := [textbookLeanCss, textbookThemeCss, textbookDetailsCss]
  extraJs := { Verso.Genre.Manual.JS.mk textbookThemeJs }

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
