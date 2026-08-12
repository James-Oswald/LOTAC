import Mathlib
import VersoManual
import Textbook.Blocks

import LOTAC2.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Textbook

#doc (Manual) "Frames and Models" =>

:::details "Notation"
To handle the notation for the various uses of the turnstile symbol, we define a typeclass `Models` that represents the satisfaction relation between two types, along with its negation. This allows us to use the turnstile symbol `⊨` to denote satisfaction and `⊭` to denote non-satisfaction in a consistent manner across different contexts.

```lean
class Models (α : Type u) (β : Type v) where
  models : α → β → Prop
infixl:51 (priority := high) " ⊨ " => Models.models

@[simp]
def Models.not_models {α : Type u} {β : Type v}
[Models α β] (a : α) (b : β) : Prop :=
  ¬(a ⊨ b)
infixl:51 (priority := high) " ⊭ " => Models.not_models
```
:::

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
We represent models as an extension of frames with a valuation function.

```lean
variable {Φ : Type}

structure Model extends Frame where
  V : Φ → S → Prop
```
:::

Another useful notion is that of a pointed model, which is a model together
with a distinguished world in the model. We will use pointed models to define
the satisfaction relation for formulas in a model. Formally, we define pointed
models as a dependent pair of a model and a world in that model.

```lean
structure PointedModel {Φ : Type} extends @Model Φ where
  w : S
notation "⟨" M ", " w "⟩ₘ" => PointedModel.mk M w

```

:::definition "Satisfaction in a Model"
Let $`M = (F, V)` be a Φ-model and let $`w` be a world in `F`.
We define the satisfaction relation $`M, w \vDash φ` for a formula `φ`
inductively as follows.

```lean
@[simp]
def PointedModel.satisfies (M : @PointedModel Φ) : L Φ → Prop
| .atom p => M.V p M.w
| ⊥ₜ       => False
| φ →ₜ ψ   => M.satisfies φ → M.satisfies ψ
| □ₜφ      => ∀ w' : M.S, M.R M.w w' →
    (⟨M.toModel, w'⟩ₘ.satisfies φ)

instance : Models (@PointedModel Φ) (L Φ) where
  models := PointedModel.satisfies

-- This helper allows us to use the notation freely in simplification.
@[simp]
theorem PointedModel.satisfies_def (M : @Model Φ) (w : M.S)  (φ : L Φ) :
(⟨M, w⟩ₘ ⊨ φ) ↔ (PointedModel.mk M w).satisfies φ := by
  rfl
```

The derived connectives are defined as follows.

```lean
@[simp]
theorem Model.satisfies_neg (M : @Model Φ) (w : M.S) (φ : L Φ) :
(⟨M, w⟩ₘ ⊭ φ) ↔ (⟨M, w⟩ₘ ⊨ ¬ₜφ) := by
  rfl

@[simp]
theorem Model.satisfies_and (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(⟨M, w⟩ₘ ⊨ (φ ∧ₜ ψ)) ↔ (⟨M, w⟩ₘ ⊨ φ) ∧ (⟨M, w⟩ₘ ⊨ ψ) := by
  simp only [L.and, L.not, PointedModel.satisfies_def, PointedModel.satisfies,
    imp_false, Classical.not_imp, not_not]

@[simp]
theorem Model.satisfies_or (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(⟨M, w⟩ₘ ⊨ (φ ∨ₜ ψ)) ↔ (⟨M, w⟩ₘ ⊨ φ) ∨ (⟨M, w⟩ₘ ⊨ ψ) := by
  simp; grind only [#aec4]

@[simp]
theorem Model.satisfies_iff (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(⟨M, w⟩ₘ ⊨ (φ ↔ₜ ψ)) ↔ ((⟨M, w⟩ₘ ⊨ φ) ↔ (⟨M, w⟩ₘ ⊨ ψ)) := by
  simp; grind only [#14f9, #7704, #4195]

@[simp]
theorem Model.satisfies_dia (M : @Model Φ) (w : M.S) (φ : L Φ) :
(⟨M, w⟩ₘ ⊨ (◇ₜ φ)) ↔ ∃ v : M.S, (M.R w v) ∧ (⟨M, v⟩ₘ ⊨ φ) := by
  classical
  simp only [Models.models, L.dia, L.not, PointedModel.satisfies]
  apply Iff.intro
  · intro h
    by_contra hnone
    apply h
    intro v hv hφ
    apply hnone
    exact ⟨v, hv, hφ⟩
  · intro h hbox
    rcases h with ⟨v, hv, hφ⟩
    exact hbox v hv hφ
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


:::definition "Truth and Validity"
A formula φ is true in a model M if it is satisfied at every world in M.
$$`M ⊨ φ ↔ ∀ w ∈ M.S, M, w ⊨ φ`

```lean
@[simp]
def L.true_in_model (φ : L Φ) (M : @Model Φ) : Prop :=
  ∀ w : M.S, ⟨M, w⟩ₘ ⊨ φ

@[simp]
instance : Models (@Model Φ) (L Φ) where
  models M φ := φ.true_in_model M
```

A formula φ is valid in a frame F if it is true in every model based on F.
$$`F ⊨ φ ↔ ∀ M, M.toFrame = F → M ⊨ φ`
```lean
@[simp]
def L.valid_in_frame (φ : L Φ) (F : Frame) : Prop :=
  ∀ M : @Model Φ, M.toFrame = F → M ⊨ φ

@[simp]
instance : Models Frame (L Φ) where
  models F φ := φ.valid_in_frame F
```

A formula φ is valid in a class of frames C if it is valid in every frame in C.
$$`C ⊨ φ ↔ ∀ F ∈ C, F ⊨ φ`
In lean we will reprsent a class as a set of frames.
```lean
@[simp]
def L.valid_in_class (φ : L Φ) (C : Set Frame) : Prop :=
  ∀ F : Frame, F ∈ C → F ⊨ φ

@[simp]
instance : Models (Set Frame) (L Φ) where
  models C φ := φ.valid_in_class C
```

We say a formula *is valid* if it is true in all models,
or equivalently, valid in the class of all frames.
```lean
@[simp]
def L.valid (φ : L Φ) : Prop :=
  ∀ M : @Model Φ, M ⊨ φ
prefix:max "⊨ " => L.valid

theorem L.valid_iff_valid_in_class (φ : L Φ) :
(⊨ φ) ↔ (Set.univ : Set Frame) ⊨ φ := by
  simp only [valid, Models.models, true_in_model, valid_in_class,
    Set.mem_univ, valid_in_frame, forall_const]
  apply Iff.intro
  · intro a F M a_1 w
    subst a_1
    simp_all only
  · intro a M w
    simp_all only
```


We have analogous definitions for truth and validity over schema.
A schema is true in a model if every instance of the schema is
true in the model.

```lean
@[simp]
def Schema.true_in_model (Γ : Set (L Φ)) (M : @Model Φ) : Prop :=
  ∀ φ ∈ Γ, M ⊨ φ
instance : Models (@Model Φ) (Set (L Φ)) where
  models M Γ := Schema.true_in_model Γ M

@[simp]
def Schema.valid (Γ : Set (L Φ)) (F : Frame) : Prop :=
  ∀ M : @Model Φ, M.toFrame = F → M ⊨ Γ
instance : Models Frame (Set (L Φ)) where
  models F Γ := Schema.valid Γ F

@[simp]
def Schema.validInClass (Γ : Set (L Φ)) (C : Set Frame) : Prop :=
  ∀ F : Frame, F ∈ C → F ⊨ Γ
instance : Models (Set Frame) (Set (L Φ)) where
  models C Γ := Schema.validInClass Γ C
```
:::



*Exercises*

1) Show that the following are true in all models,
   hence valid in all frames.
* $`□⊤`
* $`□(φ → ψ) → (□φ → □ψ)`
* $`◇(φ → ψ) → (□φ → ◇ψ)`
* $`□(φ → ψ) → (◇φ → ◇ψ)`
* $`□(φ ∧ ψ) ↔ (□φ ∧ □ψ)`
* $`◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)`

:::details "Solutions"
```lean
example (M : @Model Φ) : M ⊨ (□ₜ(⊤ₜ : L Φ)) := by
  change ∀ w : M.S, ⟨M, w⟩ₘ ⊨ (□ₜ(⊤ₜ : L Φ))
  intro w v hv hbot
  exact hbot

example (M : @Model Φ) (φ ψ : L Φ) :
M ⊨ (□ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ □ₜψ)) := by
  change ∀ w : M.S,
    ⟨M, w⟩ₘ ⊨ (□ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ □ₜψ))
  intro w hbox hφ v hv
  exact hbox v hv (hφ v hv)

example (M : @Model Φ) (φ ψ : L Φ) :
M ⊨ (◇ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ ◇ₜψ)) := by
  change ∀ w : M.S,
    ⟨M, w⟩ₘ ⊨ (◇ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ ◇ₜψ))
  intro w hdia hbox
  rcases (M.satisfies_dia w (φ →ₜ ψ)).mp hdia with ⟨v, hv, himp⟩
  exact (M.satisfies_dia w ψ).mpr ⟨v, hv, himp (hbox v hv)⟩

example (M : @Model Φ) (φ ψ : L Φ) :
M ⊨ (□ₜ(φ →ₜ ψ) →ₜ (◇ₜφ →ₜ ◇ₜψ)) := by
  change ∀ w : M.S,
    ⟨M, w⟩ₘ ⊨ (□ₜ(φ →ₜ ψ) →ₜ (◇ₜφ →ₜ ◇ₜψ))
  intro w hbox hdia
  rcases (M.satisfies_dia w φ).mp hdia with ⟨v, hv, hφ⟩
  exact (M.satisfies_dia w ψ).mpr ⟨v, hv, hbox v hv hφ⟩

example (M : @Model Φ) (φ ψ : L Φ) :
M ⊨ (□ₜ(φ ∧ₜ ψ) ↔ₜ (□ₜφ ∧ₜ □ₜψ)) := by
  change ∀ w : M.S, ⟨M, w⟩ₘ ⊨ (□ₜ(φ ∧ₜ ψ) ↔ₜ (□ₜφ ∧ₜ □ₜψ))
  intro w
  rw [Model.satisfies_iff, Model.satisfies_and]
  constructor
  · intro h
    constructor
    · intro v hv
      exact (M.satisfies_and v φ ψ).mp (h v hv) |>.left
    · intro v hv
      exact (M.satisfies_and v φ ψ).mp (h v hv) |>.right
  · intro h v hv
    exact (M.satisfies_and v φ ψ).mpr ⟨h.left v hv, h.right v hv⟩

example (M : @Model Φ) (φ ψ : L Φ) :
M ⊨ (◇ₜ(φ ∨ₜ ψ) ↔ₜ (◇ₜφ ∨ₜ ◇ₜψ)) := by
  change ∀ w : M.S, ⟨M, w⟩ₘ ⊨ (◇ₜ(φ ∨ₜ ψ) ↔ₜ (◇ₜφ ∨ₜ ◇ₜψ))
  intro w
  rw [Model.satisfies_iff, Model.satisfies_or]
  apply Iff.intro
  · case mp =>
    intro h
    rcases (M.satisfies_dia w (φ ∨ₜ ψ)).mp h with ⟨v, hv, hφψ⟩
    cases (M.satisfies_or v φ ψ).mp hφψ with
    | inl hφ => exact Or.inl ((M.satisfies_dia w φ).mpr ⟨v, hv, hφ⟩)
    | inr hψ => exact Or.inr ((M.satisfies_dia w ψ).mpr ⟨v, hv, hψ⟩)
  · case mpr =>
    intro h
    cases h with
    | inl hφ =>
      rcases (M.satisfies_dia w φ).mp hφ with ⟨v, hv, hφv⟩
      exact (M.satisfies_dia w (φ ∨ₜ ψ)).mpr
        ⟨v, hv, (M.satisfies_or v φ ψ).mpr (Or.inl hφv)⟩
    | inr hψ =>
      rcases (M.satisfies_dia w ψ).mp hψ with ⟨v, hv, hψv⟩
      exact (M.satisfies_dia w (φ ∨ₜ ψ)).mpr
        ⟨v, hv, (M.satisfies_or v φ ψ).mpr (Or.inr hψv)⟩
```
:::

2) Show that the following do not hold in all frames by providing a countermodel.
* $`□φ → φ`
* $`□(φ → ψ) → (□φ → □ψ)`
* $`◇⊤`
* $`◇φ → □φ`
* $`□(□φ → ψ) ∨ (□ψ → □φ)`
* $`□(φ ∨ ψ) → (□φ ∨ □ψ)`
* $`□(□φ → φ) → □φ`

:::details "Solutions"
```lean
example (M : @Model Φ) (φ : L Φ) : M ⊭ (□ₜφ →ₜ φ) := by
  sorry
```
:::
