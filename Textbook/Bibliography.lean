import Lean.Elab.Command
import Std.Internal.Parsec
import Std.Internal.Parsec.String
import VersoManual

open Lean Elab Command Term
open Std.Internal.Parsec Std.Internal.Parsec.String
open Verso.Genre.Manual

namespace Textbook

/-! A deliberately small BibTeX parser for the entry syntax used by Verso. -/

private structure BibField where
  name : String
  content : String

private structure BibEntry where
  category : String
  key : String
  fields : List BibField

namespace BibParser

private def noneOf (bad : String) : Parser Char := satisfy (fun c => !bad.contains c)

private def asciiAlphaNum : Parser Char := attempt do
  let c ← any
  if c.isAlphanum && c.toNat < 128 then pure c else fail "ASCII letter or digit expected"

private def wordToLower : Parser String :=
  String.map Char.toLower <$> manyChars asciiLetter

private partial def bracedTail (acc : String) : Parser String := attempt do
  let c ← any
  if c == '{' then
    let nested ← bracedTail ""
    bracedTail (acc ++ "{" ++ nested)
  else if c == '}' then
    pure (acc ++ "}")
  else
    bracedTail (acc.push c)

private def braced : Parser String := attempt do
  skipChar '{'
  return (← bracedTail "").dropEnd 1 |>.copy

private partial def quotedTail (acc : String) (escaped : Bool := false) : Parser String := do
  let c ← any
  if c == '"' && !escaped then pure acc
  else quotedTail (acc.push c) (c == '\\' && !escaped)

private def quoted : Parser String := attempt do
  skipChar '"'
  quotedTail ""

private def bare : Parser String := manyChars (noneOf ",}\n\r\t ")

private def value : Parser String := attempt do
  match ← peek! with
  | '{' => braced
  | '"' => quoted
  | _ => bare

private def field : Parser BibField := attempt do
  let name ← manyChars (asciiAlphaNum <|> pchar '_' <|> pchar '-')
  ws
  skipChar '='
  ws
  return ⟨name.toLower, ← value⟩

private def key : Parser String :=
  many1Chars (asciiAlphaNum <|> pchar ':' <|> pchar '-' <|> pchar '_')

private partial def fields (acc : List BibField := []) : Parser (List BibField) := do
  ws
  if (← peek!) == '}' then pure acc.reverse
  else
    let next ← field
    ws
    if (← peek!) == ',' then skipChar ','
    fields (next :: acc)

private def entry : Parser BibEntry := attempt do
  skipChar '@'
  let category ← wordToLower
  ws
  skipChar '{'
  ws
  let key ← key
  skipChar ','
  let fields ← fields
  skipChar '}'
  return ⟨category, key, fields⟩

private partial def fileCore (acc : List BibEntry) : Parser (List BibEntry) := do
  let _ ← manyChars (noneOf "@")
  if (← peek?).isNone then pure acc.reverse
  else fileCore ((← entry) :: acc)

def file : Parser (List BibEntry) := fileCore []

end BibParser

private def article
    (title : String) (authors : Array String) (journal : String) (year : Int)
    (month volume number : String) (pages : Option (Nat × Nat)) (url : Option String) : Article where
  title := .text title
  authors := authors.map (.text ·)
  journal := .text journal
  year := year
  month := if month.isEmpty then none else some (.text month)
  volume := .text volume
  number := .text number
  pages := pages
  url := url

private def inProceedings
    (title : String) (authors : Array String) (year : Int) (booktitle : String)
    (url : Option String) : InProceedings where
  title := .text title
  authors := authors.map (.text ·)
  year := year
  booktitle := .text booktitle
  url := url

private def thesis
    (title author : String) (year : Int) (university degree : String)
    (url : Option String) : Thesis where
  title := .text title
  author := .text author
  year := year
  university := .text university
  degree := .text degree
  url := url

private def arXiv
    (title : String) (authors : Array String) (year : Int) (id : String) : ArXiv where
  title := .text title
  authors := authors.map (.text ·)
  year := year
  id := id

private def field? (tags : List BibField) (name : String) : Option String :=
  (tags.find? (·.name == name)).map (·.content)

private def field (key : String) (tags : List BibField) (name : String) : CommandElabM String :=
  match field? tags name with
  | some value => pure value
  | none => throwError "BibTeX entry '{key}' is missing its '{name}' field"

private def authorName (name : String) : String :=
  let name := name.replace "\\{" "" |>.replace "\\}" ""
  match name.splitOn "," with
  | [last, first] => s!"{first.trimAscii} {last.trimAscii}"
  | _ => name.trimAscii.toString

private def authors (value : String) : Array String :=
  (value.splitOn " and ").map authorName |>.toArray

private def year (key value : String) : CommandElabM Int :=
  match value.toInt? with
  | some value => pure value
  | none => throwError "BibTeX entry '{key}' has invalid year '{value}'"

private def pages (value : Option String) : Option (Nat × Nat) := do
  let value ← value
  let doubleDash := value.splitOn "--"
  let bounds := if doubleDash.length == 2 then doubleDash else value.splitOn "-"
  match bounds with
  | [first, last] => some (← first.trimAscii.toNat?, ← last.trimAscii.toNat?)
  | _ => none

private def url (tags : List BibField) : Option String :=
  (field? tags "url").filter (!·.isEmpty) <|>
    ((fun doi => s!"https://doi.org/{doi}") <$> (field? tags "doi").filter (!·.isEmpty))

private def declareArticle (key : String) (tags : List BibField) : CommandElabM Unit := do
  let title ← field key tags "title"
  let authorSyntax : Array (TSyntax `term) := (authors (← field key tags "author")).map quote
  let journal ← field key tags "journal"
  let year ← year key (← field key tags "year")
  let month := (field? tags "month").getD ""
  let volume := (field? tags "volume").getD ""
  let number := (field? tags "number").getD ""
  let pages := pages (field? tags "pages")
  let url := url tags
  elabCommand (← `(def $(mkIdent (.mkSimple key)) : Article :=
    article $(quote title) #[$authorSyntax,*] $(quote journal) $(quote year)
      $(quote month) $(quote volume) $(quote number) $(quote pages) $(quote url)))

private def declareInProceedings (key : String) (tags : List BibField) : CommandElabM Unit := do
  let title ← field key tags "title"
  let authorSyntax : Array (TSyntax `term) := (authors (← field key tags "author")).map quote
  let year ← year key (← field key tags "year")
  let booktitle ← field key tags "booktitle"
  let url := url tags
  elabCommand (← `(def $(mkIdent (.mkSimple key)) : InProceedings :=
    inProceedings $(quote title) #[$authorSyntax,*] $(quote year) $(quote booktitle) $(quote url)))

private def declareBookLike
    (key : String) (tags : List BibField) (containerField : String) : CommandElabM Unit := do
  let title ← field key tags "title"
  let authorValue ←
    match field? tags "author" <|> field? tags "editor" with
    | some value => pure value
    | none => throwError "BibTeX entry '{key}' is missing its 'author' or 'editor' field"
  let authorSyntax : Array (TSyntax `term) := (authors authorValue).map quote
  let year ← year key (← field key tags "year")
  let booktitle :=
    (field? tags containerField <|> field? tags "publisher" <|> field? tags "series").getD ""
  let url := url tags
  elabCommand (← `(def $(mkIdent (.mkSimple key)) : InProceedings :=
    inProceedings $(quote title) #[$authorSyntax,*] $(quote year) $(quote booktitle) $(quote url)))

private def declareThesis
    (key : String) (tags : List BibField) (degree : String) : CommandElabM Unit := do
  let title ← field key tags "title"
  let authorList := authors (← field key tags "author")
  let some author := authorList[0]?
    | throwError "BibTeX entry '{key}' has no author"
  let year ← year key (← field key tags "year")
  let university ← field key tags "school"
  let url := url tags
  elabCommand (← `(def $(mkIdent (.mkSimple key)) : Thesis :=
    thesis $(quote title) $(quote author) $(quote year) $(quote university) $(quote degree) $(quote url)))

private def declareArXiv (key : String) (tags : List BibField) : CommandElabM Unit := do
  let title ← field key tags "title"
  let authorSyntax : Array (TSyntax `term) := (authors (← field key tags "author")).map quote
  let year ← year key (← field key tags "year")
  let id ← field key tags "eprint"
  elabCommand (← `(def $(mkIdent (.mkSimple key)) : ArXiv :=
    arXiv $(quote title) #[$authorSyntax,*] $(quote year) $(quote id)))

private def declareEntry (entry : BibEntry) : CommandElabM Unit :=
    match entry.category with
    | "article" => declareArticle key tags
    | "inproceedings" | "conference" => declareInProceedings key tags
    -- Verso v4.33 has no native book/in-collection value. `InProceedings` is
    -- its closest author/title/container/year representation.
    | "book" => declareBookLike key tags "publisher"
    | "inbook" | "incollection" => declareBookLike key tags "booktitle"
    | "phdthesis" => declareThesis key tags "PhD thesis"
    | "mastersthesis" => declareThesis key tags "Master's thesis"
    | "misc" =>
      if (field? tags "archiveprefix").map (·.toLower) == some "arxiv" || (field? tags "eprint").isSome then
        declareArXiv key tags
      else
        throwError "BibTeX entry '{key}' is an unsupported 'misc' entry (only arXiv entries are supported)"
    | _ => throwError "BibTeX entry '{key}' has unsupported type '{entry.category}'"
  where
    key := entry.key
    tags := entry.fields

syntax (name := loadBibTeX) "#load_bibtex " term : command

@[command_elab loadBibTeX]
unsafe def elabLoadBibTeX : CommandElab
  | `(#load_bibtex $source:term) => do
    let source ← liftTermElabM <| evalTerm String (.const ``String []) source
    match BibParser.file ⟨source, source.startPos⟩ with
    | .success _ entries => entries.forM declareEntry
    | .error _ message => throwError "Could not parse bibliography: {message}"
  | _ => throwUnsupportedSyntax

-- `include_str` makes `references.bib` the sole source of bibliography data.
#load_bibtex (include_str "../references.bib")

namespace Bibliography

/-!
`{cite key}[]` leaves only Verso's numbered margin-note marker in the prose and
places the full bibliographic citation in the margin. The marker and margin
entry share one page-order number with ordinary margin notes and Verso's other
citation roles.
-/

private def marginaliaCounterCss := r#"
/*
Verso v4.33's CSS counter is scoped inconsistently across marginalia produced
by different inline extensions. JavaScript assigns one page-order number to
both the marker and its note; these rules display that explicit number.
*/
.marginalia,
.marginalia .note {
  counter-increment: none !important;
}

.marginalia::after {
  content: attr(data-margin-number) !important;
}

.marginalia .note::before {
  content: attr(data-margin-number) "." !important;
}
"#

private def marginaliaCounterJs := r#"
document.addEventListener("DOMContentLoaded", () => {
  document.querySelectorAll(".marginalia").forEach((marginalia, index) => {
    const number = String(index + 1);
    marginalia.setAttribute("data-margin-number", number);
    const note = marginalia.querySelector(".note");
    if (note) note.setAttribute("data-margin-number", number);
  });
});
"#

inline_extension Verso.Genre.Manual.Inline.numberedMargin where
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun go _ _ content => do
      pure <| Verso.Genre.Manual.Marginalia.TeX (← content.mapM go)
  extraCss := [Verso.Genre.Manual.Marginalia.css, marginaliaCounterCss]
  extraJs := { Verso.Genre.Manual.JS.mk marginaliaCounterJs }
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ _ content => do
      Verso.Genre.Manual.Marginalia.html <$> content.mapM go

@[role]
meta def cite : Verso.Doc.Elab.RoleExpanderOf
    Verso.Genre.Manual.Bibliography.CiteConfig
  | config, _ => do
    let citations := config.citations.map mkIdent |>.toArray
    let citation ←
      ``(Verso.Doc.Inline.other
          (Verso.Genre.Manual.Bibliography.Inline.cite
            ([$citations,*] : List Verso.Genre.Manual.Bibliography.Citable)
            Verso.Genre.Manual.Bibliography.Style.here)
          #[])
    ``(Verso.Doc.Inline.other Verso.Genre.Manual.Inline.numberedMargin #[$citation])

end Textbook.Bibliography
