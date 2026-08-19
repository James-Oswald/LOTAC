import VersoManual

open Lean
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace Textbook

structure NotationEntry where
  display : String
  expansion : String
  sectionTitle : String
  canonicalSection : String
deriving ToJson, FromJson

private def normalizeSpaces (s : String) : String :=
  " ".intercalate <| (s.splitOn " ").filter (not ∘ String.isEmpty)

private def cleanNotation (s : String) : String :=
  let s := normalizeSpaces (s.replace "\"" "")
  s.replace "[ " "[" |>.replace " ]" "]"
    |>.replace "( " "(" |>.replace " )" ")"
    |>.replace "{ " "{" |>.replace " }" "}"

private def quotedSymbol? (s : String) : Option String :=
  match s.splitOn "\"" with
  | _before :: symbol :: _after => some symbol.trimAscii.toString
  | _ => none

private def notationFromLine? (line : String) : Option (String × String) := do
  let line := line.trimAscii.toString
  if line.startsWith "local " || line.startsWith "scoped[" then none else
  let words := (line.splitOn " ").filter (not ∘ String.isEmpty)
  let kind ← words.head?
  unless kind == "notation" || kind.startsWith "infix" ||
      kind.startsWith "prefix" || kind.startsWith "postfix" do
    none
  let rest := (line.drop kind.length).trimAscii.toString
  let pieces := rest.splitOn "=>"
  let lhs ← pieces.head?
  let rhs := "=>".intercalate pieces.tail |>.trimAscii.toString
  guard !rhs.isEmpty
  let display? :=
    if kind.startsWith "infix" then
      quotedSymbol? lhs |>.map fun symbol => s!"_ {symbol} _"
    else if kind.startsWith "prefix" then
      quotedSymbol? lhs |>.map fun symbol => s!"{symbol} _"
    else if kind.startsWith "postfix" then
      quotedSymbol? lhs |>.map fun symbol => s!"_ {symbol}"
    else
      some (cleanNotation lhs)
  let display ← display?
  return (display, rhs)

private def notationsInSource (source : String) : Array (String × String) :=
  source.splitOn "\n" |>.toArray.filterMap notationFromLine?

private partial def notationsInBlock (block : Doc.Block Manual) : Array (String × String) :=
  match block with
  | .other container contents =>
      if container.name == ``Verso.Genre.Manual.InlineLean.Block.lean then
        contents.flatMap fun
          | .code source => notationsInSource source
          | child => notationsInBlock child
      else
        contents.flatMap notationsInBlock
  | .blockquote contents | .concat contents => contents.flatMap notationsInBlock
  | .ul items | .ol _ items =>
      items.flatMap fun ⟨contents⟩ => contents.flatMap notationsInBlock
  | .dl items =>
      items.flatMap fun ⟨_, contents⟩ => contents.flatMap notationsInBlock
  | .para _ | .code _ => #[]

private def canonicalSectionName (rootTitle : String) (path : Array String) : String :=
  ("--".intercalate (rootTitle :: path.toList)).sluggify.toString

partial def collectNotationEntries
    (rootTitle : String) (source : Doc.Part Manual) : Array NotationEntry :=
  go #[] source |>.foldl (init := #[]) fun entries entry =>
    if entries.any fun old => old.display == entry.display &&
        old.expansion == entry.expansion then
      entries
    else
      entries.push entry
where
  go (parents : Array String) (part : Doc.Part Manual) : Array NotationEntry :=
    let path := parents.push part.titleString
    let here := part.content.flatMap notationsInBlock |>.map fun (display, expansion) =>
      { display, expansion, sectionTitle := part.titleString,
        canonicalSection := canonicalSectionName rootTitle path }
    here ++ part.subParts.flatMap (go path)

private def notationGlossaryCss := r#"
.notation-glossary {
  margin: 1.25rem 0;
}

.notation-glossary-row {
  display: grid;
  grid-template-columns: minmax(8rem, 14rem) 1fr;
  gap: 0.35rem 1rem;
  padding: 0.65rem 0;
  border-bottom: 1px solid color-mix(in srgb, currentColor 16%, transparent);
}

.notation-glossary-row dt,
.notation-glossary-row dd {
  margin: 0;
}

.notation-glossary-row dt code {
  font-size: 1.05em;
  font-weight: 600;
}

.notation-glossary-expansion {
  display: block;
  margin-top: 0.2rem;
  color: color-mix(in srgb, currentColor 72%, transparent);
  font-size: 0.9em;
}

@media screen and (max-width: 600px) {
  .notation-glossary-row {
    grid-template-columns: 1fr;
  }
}
"#

block_extension Block.notationGlossary (entries : Array NotationEntry) where
  data := ToJson.toJson entries
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => open Verso.Output.Html in do
    let entries : Array NotationEntry ←
      match FromJson.fromJson? data with
      | .ok entries => pure entries
      | .error err => reportError err; pure #[]
    let entries := entries.qsort fun a b => a.display.toLower < b.display.toLower
    let rows ← entries.mapM fun entry => do
      let href ←
        match (← Doc.Html.HtmlT.state).resolveDomainObject
            sectionDomain entry.canonicalSection with
        | .ok link => pure link.relativeLink
        | .error err => do
            reportError s!"Could not link notation {entry.display}: {err}"
            pure "#"
      pure {{
        <div class="notation-glossary-row">
          <dt><code>{{s!"{entry.display}"}}</code></dt>
          <dd>
            "Defined in "<a href={{href}}>{{s!"{entry.sectionTitle}"}}</a>"."
            <span class="notation-glossary-expansion">
              "Expands to "<code>{{s!"{entry.expansion}"}}</code>
            </span>
          </dd>
        </div>
      }}
    pure {{<dl class="notation-glossary">{{rows}}</dl>}}
  extraCss := [notationGlossaryCss]

structure NotationGlossaryConfig where
  source : Ident
  rootTitle : StrLit

instance : FromArgs NotationGlossaryConfig DocElabM where
  fromArgs := NotationGlossaryConfig.mk <$>
    .positional `source .ident "document containing notation declarations" <*>
    .positional `rootTitle .strLit

@[directive]
meta def notationGlossary : DirectiveExpanderOf NotationGlossaryConfig
  | {source, rootTitle}, _ =>
    ``(Verso.Doc.Block.other
        (Block.notationGlossary
          (collectNotationEntries $(quote rootTitle.getString) (%doc $source))) #[])

end Textbook
