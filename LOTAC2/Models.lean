import Mathlib
import VersoManual
import Textbook.Blocks

import LOTAC2.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Textbook

#doc (Manual) "Frames and Models" =>


:::definition "Frames and Models"

A frame is a pair $`(S, R)` where `S` is a non-empty set of worlds and $R$ is
a binary relation on $`S` called the accessibility relation.

```lean
structure Frame where
  S : Type
  S_nonempty : Nonempty S
  R : S → S → Prop
```

A Φ-model is a pair $`(F, V)` where `F` is a frame and `V` is a valuation
function that assigns to each propositional variable a set of worlds in `F`.

```lean
variable {Φ : Type}

structure Model extends Frame where
  V : Φ → S → Prop
```
:::

:::definition "Satisfaction in a Model"
Let $`M = (F, V)` be a Φ-model and let $`w` be a world in `F`.
We define the satisfaction relation $`M, w \vDash φ` for a formula `φ`
inductively as follows.

```lean
@[simp]
def Model.satisfies (M : @Model Φ) (w : M.S) : L Φ → Prop
| .atom p => M.V p w
| ⊥ₜ       => False
| φ →ₜ ψ   => M.satisfies w φ → M.satisfies w ψ
| □ₜφ     => ∀ v : M.S, (M.R w v) → (M.satisfies v φ)

notation  M "⊨[" w "]" φ => Model.satisfies M w φ

def Model.not_satisfies (M : @Model Φ) (w : M.S) (φ : L Φ) : Prop :=
  ¬Model.satisfies M w φ

notation  M " ⊭[" w "] " φ => Model.not_satisfies M w φ
```

The derived connectives are defined as follows.

```lean
@[simp]
theorem Model.satisfies_neg (M : @Model Φ) (w : M.S) (φ : L Φ) :
(M ⊭[w] φ) ↔ (M ⊨[w] ¬ₜ φ) := by
  rfl

@[simp]
theorem Model.satisfies_and (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] φ ∧ₜ ψ) ↔ (M ⊨[w] φ) ∧ (M ⊨[w] ψ) := by
  simp only [L.and, L.not, satisfies, imp_false, Classical.not_imp, not_not]

@[simp]
theorem Model.satisfies_or (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] φ ∨ₜ ψ) ↔ (M ⊨[w] φ) ∨ (M ⊨[w] ψ) := by
  simp only [L.or, L.not, L.and, satisfies]
  grind only [#8eb5]

@[simp]
theorem Model.satisfies_iff (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] φ ↔ₜ ψ) ↔ ((M ⊨[w] φ) ↔ (M ⊨[w] ψ)) := by
  simp only [L.iff, L.and, L.not, satisfies]
  grind only [#5ede, #004e]

@[simp]
theorem Model.satisfies_dia (M : @Model Φ) (w : M.S) (φ : L Φ) :
(M ⊨[w] ◇ₜ φ) ↔ ∃ v : M.S, (M.R w v) ∧ (M ⊨[v] φ) := by
  simp only [L.dia, L.not, satisfies]
  grind only [#3e50, #0e31]
```
:::


:::definition "Quasi-atomic Formulae"
A formula is quasi-atomic if it is either atomic or begins with a box.
```lean
def L.isQuasiAtomic {Φ : Type} : L Φ → Prop
| .atom _ => True
| .box _ => True
| _ => False
```

:::
