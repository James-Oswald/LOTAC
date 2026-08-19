import VersoManual
import Textbook.Bibliography
import MDML.PML
import MDML.NotationGlossary

open Verso.Genre Manual
open Textbook
open Textbook.Bibliography
open scoped Verso.Doc.Concrete

def MDML := verso (Manual) "Many Dimensional Modal Logics In Lean"
:::::::

%%%
authors := ["James Oswald"]
%%%

MDML is a textbook about modal logic whose definitions, examples,
and proofs are checked by Lean. The book is named after the famous modal logic
textbook "Many Dimensional Modal Logics : Theory and Applications"
{cite Gabbay2003b}[]. The book also pulls heavily from Goldblatt's
"Logics of Time and Computation"{cite Goldblatt1992}[].

*Philosophy*

MDML takes a _Deep Embedding_ approach to formalizing many-dimensional modal
logics in Lean, meaning that we explicitly represent the syntax and semantics of
the logic within the proof assistant, rather than relying on Lean's built-in
logical framework.

*Notation and Notational Convention*

We love notation. We will heavily use notation to allow for concise theorems,
for example, the theorem that "Any propositional modal tautology is a
subsitution instance of a propositional tautology" is written:
$$`⊢_\texttt{t} φ ↔ ∃ ψ, ⊢_\texttt{p} ψ ∧ φ ≼_\texttt{s} ψ`
Where $`⊢_\texttt{t}` denotes being a tautology,
and $`⊢_\texttt{p}` denotes being a propositional tautology,
and while $`φ ≼_\texttt{s} ψ` denotes that $`φ`$ is a substitution
instance of $`ψ`.

We keep our notation explicit. In most texts readers will be familiar with "$`⊨`"
(the vDash / semantic entailment / models symbol) being overloaded to mean
everything from truth at a world to validity of a schema in a frame. We opt
instead for explicit notation for each level i.e. using "$`⊨^\texttt{m}`" for
truth in a model and "$`⊨^\texttt{f}`" for truth in a frame etc.

As you can see we like to use letters in our notations, this is a consequence
of trying to line up our Lean notation with our mathematical notation. To make it
clear when we are using a letter as part of a notation, we will have the
letter appear in monospaced font as can be seen above. When a letter is not
in monospaced font, it can be assumed to be a variable, for example evaluation
of a formula $`φ` under a quasi-atomic valuation $`v`is written $`⟦φ⟧_v`. $`v` is
a variable here representing the valuation.

For readers worried about notation chasing, we have done our best to make it
easy to follow notation back to the underlying Lean definitions.
We will typically provide our definition and theorem statements three times:
once in natural language, once using our notation, and once in Lean.
Where possible, we will have the mathematical notation match our Lean notation.
In the event notation can't be chased back, we provide a glossary.

*Citing*

If you use MDML in your research or teaching, please cite it as follows:

```
@book{Oswald2024,
  author    = {James Oswald},
  title     = {Many Dimensional Modal Logics In Lean},
  year      = {2026},
  url       = {https://github.com/James-Oswald/MDML}
}
```

{include 1 MDML.PML}
{include 1 MDML.NotationGlossary}
:::::::

def main := manualMain MDML.toPart
