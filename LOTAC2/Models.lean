import Mathlib
import VersoManual
import Textbook.Blocks

import LOTAC2.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Textbook

#doc (Manual) "Frames and Models" =>

# Frames and Models, Truth and Validity
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
@[simp]
def L.isQuasiAtomic {Φ : Type} : L Φ → Prop
| .atom _ => True
| .box _ => True
| _ => False
```

A Quasi-atomic subformula valuation is a valuation function that assigns
true or false to each quasi-atomic subformula of a formula.

```lean
abbrev QuasiAtomicSubformulaValuation [Denumerable Φ] (φ : L Φ) : Type :=
  (ψ : L Φ) → ψ.isQuasiAtomic → ψ ∈ φ.subformulae → Prop

```
Given a quasi-atomic valuation `V`, we can extend it to a valuation of
an arbitrary formula `φ`. To do this, we need to be able to lift
valuations on implications to valuations on their left and right subformulae.
The following definitions provide this lifting.
```lean
/--
Given a quasi-atomic subformula valuation of an implication,
return a valuation over subformulae of the left-hand side of the implication.
 -/
def QuasiAtomicSubformulaValuation.left
[Denumerable Φ] {φ ψ : L Φ}
(V : QuasiAtomicSubformulaValuation (φ →ₜ ψ)) :
QuasiAtomicSubformulaValuation φ :=
  fun χ hqa hχ => V χ hqa (by
    simp only [L.subformulae, Finset.mem_union,
      Finset.mem_singleton]
    exact Or.inl (Or.inr hχ))

def QuasiAtomicSubformulaValuation.right
[Denumerable Φ] {φ ψ : L Φ}
(V : QuasiAtomicSubformulaValuation (φ →ₜ ψ)) :
QuasiAtomicSubformulaValuation ψ :=
  fun χ hqa hχ => V χ hqa (by
    simp only [L.subformulae, Finset.mem_union,
      Finset.mem_singleton]
    exact Or.inr hχ)
```
With these we can then define the extended valuation.
```lean
def ExtendQuasiAtomicValuation [Denumerable Φ]
 (φ : L Φ) (V : QuasiAtomicSubformulaValuation φ) : Prop :=
match h: φ with
| .atom p => V (.atom p)
  (by simp only [L.isQuasiAtomic])
  (by simp only [L.subformulae, Finset.mem_singleton])
| .box φ => V (.box φ)
  (by simp only [L.isQuasiAtomic])
  (by apply L.subformulae_mem_refl)
| .bot => False
| .imp φ ψ =>
  (ExtendQuasiAtomicValuation φ V.left) →
    (ExtendQuasiAtomicValuation ψ V.right)
```
:::

:::definition "Tautologies"
We can define the notion of tautology in terms of quasi-atomic subformulae.
We say a formula φ is a tautology if its extended valuation is true for
every valuation of its quasi-atomic subformula. This idea naturally
coresponds to the notion of tautology in propositional logic, where a formula
is a tautology if it is true under every assignment of truth values to
its propositional variables, except now we consider quasi-atomic subformulae
instead.
```lean
def L.isTautology [Denumerable Φ] (φ : L Φ) : Prop :=
  ∀ V : QuasiAtomicSubformulaValuation φ, ExtendQuasiAtomicValuation φ V
```
:::

A consequence of this is that any tautology is a subsitution instance of
a "box-free" tautology, i.e. a tautolohy in propositional logic.

:::details "Proof"
```lean
@[simp]
def L.boxFree : L Φ → Prop
| .atom _ => True
| .bot => True
| .imp φ ψ => φ.boxFree ∧ ψ.boxFree
| .box _ => False

theorem L.subst_boxFree_tautology
[Denumerable Φ] (φ : L Φ) (h1 : φ.isTautology) :
∃ (ψ : L Φ), ψ.boxFree ∧ ψ.isTautology ∧ φ.isSubstInstance ψ := by
  classical
  let name (A : L Φ) := Denumerable.ofNat Φ (Encodable.encode A)
  let erase : L Φ → L Φ := L.rec
    (fun p => .atom (name (.atom p))) .bot
    (fun _ _ A B => A →ₜ B)
    (fun A _ => .atom (name (.box A)))
  let eval : L Φ → (L Φ → Prop) → Prop := L.rec
    (fun p V => V (.atom p)) (fun _ => False)
    (fun _ _ VA VB V => VA V → VB V)
    (fun A _ V => V (.box A))
  have congr : ∀ (A : L Φ) V W,
      (∀ B hq hB hB', V B hq hB = W B hq hB') →
      (ExtendQuasiAtomicValuation A V ↔
        ExtendQuasiAtomicValuation A W) := by
    intro A; induction A with
    | atom p => intros; exact iff_of_eq (by apply_assumption)
    | bot => simp [ExtendQuasiAtomicValuation]
    | box A => intros; exact iff_of_eq (by apply_assumption)
    | imp A B ihA ihB =>
        intro V W h
        simp only [ExtendQuasiAtomicValuation]
        rw [ihA V.left W.left, ihB V.right W.right]
        all_goals intros; apply h
  have total : ∀ (A : L Φ) (V : L Φ → Prop),
      ExtendQuasiAtomicValuation A (fun B _ _ => V B) ↔ eval A V := by
    intro A; induction A with
    | atom p => intro V; rfl
    | bot => intro V; rfl
    | box A => intro V; rfl
    | imp A B ihA ihB =>
        intro V
        simp only [ExtendQuasiAtomicValuation, eval]
        rw [congr A _ (fun C _ _ => V C),
          congr B _ (fun C _ _ => V C), ihA, ihB]
        all_goals intros; rfl
  have free : ∀ A, (erase A).boxFree := by
    intro A; induction A <;> simp_all [erase]
  have rename : ∀ A V, eval (erase A) V ↔
      eval A (fun B => V (.atom (name B))) := by
    intro A; induction A <;> simp_all [erase, eval]
  have subst : ∀ A, A = L.subst
      (fun p => (Encodable.decode (Encodable.encode p)).getD (.atom p))
      (erase A) := by
    intro A; induction A with
    | atom p =>
        simp [erase, name, L.subst, Denumerable.encode_ofNat]
    | bot => rfl
    | imp A B ihA ihB =>
        simp only [erase, L.subst, L.imp.injEq]
        exact ⟨ihA, ihB⟩
    | box A =>
        simp [erase, name, L.subst, Denumerable.encode_ofNat]
  refine ⟨erase φ, free φ, ?_, ⟨_, subst φ⟩⟩
  · intro W
    let V : L Φ → Prop := fun A =>
      if hqa : A.isQuasiAtomic then
        if hA : A ∈ (erase φ).subformulae then W A hqa hA
        else False
      else False
    rw [congr _ W (fun A _ _ => V A)]
    · rw [total, rename, ← total]
      exact h1 (fun A _ _ => V (.atom (name A)))
    · intro A hqa hA hA'
      simp only [V, dif_pos hqa, dif_pos hA]
```
:::
