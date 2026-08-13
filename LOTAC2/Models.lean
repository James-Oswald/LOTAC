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
  [S_nonempty : Nonempty S]
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

```lean -show
open Illuminate

private def decideToBool (d : Decidable p) : Bool :=
  match d with
  | .isTrue _ => true
  | .isFalse _ => false

private def subscriptDigit : Char → Char
  | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
  | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉'
  | c => c

private def worldLabel (i : Nat) : String :=
  "w" ++ String.ofList ((toString i).toList.map subscriptDigit)

/-- Automatically render a finite model. -/
def Model.diagram (M : @Model Φ) [FinEnum M.S] [Denumerable Φ]
    [decideR : DecidableRel M.R]
    [decideV : ∀ p w, Decidable (M.V p w)] : Diagram SVG :=
  let cfg : StateDiagramConfig :=
    { radius := 24, spacing := 100 }
  let worlds := FinEnum.toList M.S
  let atoms : List (Φ × String) :=
    [(Denumerable.ofNat Φ 0, "φ"),
      (Denumerable.ofNat Φ 1, "ψ"),
      (Denumerable.ofNat Φ 2, "χ")]
  let nodes := worlds.zipIdx.map fun (w, i) =>
    let trueAtoms := atoms.filterMap fun (p, label) =>
      if decideToBool (decideV p w) then
        some label
      else none
    let valuation :=
      if trueAtoms.isEmpty then "∅"
      else ", ".intercalate trueAtoms
    cfg.state i s!"{worldLabel i}\n{valuation}"
  let edges := worlds.zipIdx.flatMap fun (w, i) =>
    worlds.zipIdx.filterMap fun (v, j) =>
      if decideToBool (decideR w v) then
        if i = j then some (cfg.loop i "")
        else if j = i + 1 then some (cfg.edge i j "")
        else if i < j then some (cfg.arc i j "" 60)
        else some (cfg.arc i j "" (-45))
      else none
  overlay (nodes ++ edges)
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
| □ₜφ      => ∀ v : M.S, M.R w v → M.satisfies v φ

notation M " ⊨[" w "] " φ => Model.satisfies M w φ
notation M " ⊭[" w "] " φ => ¬ M ⊨[w] φ

```
Thus `M ⊨[w] φ` says that `φ` is satisfied at `w`, while
`M ⊭[w] φ` says that it is not satisfied there.

The derived connectives are defined as follows.

```lean
theorem Model.satisfies_neg (M : @Model Φ) (w : M.S) (φ : L Φ) :
(M ⊭[w] φ) ↔ (M ⊨[w] ¬ₜφ) := by
  rfl

@[simp]
theorem Model.satisfies_and (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] (φ ∧ₜ ψ)) ↔ (M ⊨[w] φ) ∧ (M ⊨[w] ψ) := by
  simp only [L.and, L.not, Model.satisfies, imp_false,
    Classical.not_imp, not_not]

@[simp]
theorem Model.satisfies_or (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] (φ ∨ₜ ψ)) ↔ (M ⊨[w] φ) ∨ (M ⊨[w] ψ) := by
  simp only [L.or, L.and, L.not, Model.satisfies,
    imp_false, Classical.not_imp, not_not]
  tauto

@[simp]
theorem Model.satisfies_iff (M : @Model Φ) (w : M.S) (φ ψ : L Φ) :
(M ⊨[w] (φ ↔ₜ ψ)) ↔ ((M ⊨[w] φ) ↔ (M ⊨[w] ψ)) := by
  simp only [L.iff, Model.satisfies_and, Model.satisfies]
  apply Iff.intro <;> grind only [cases Or]

@[simp]
theorem Model.satisfies_dia (M : @Model Φ) (w : M.S) (φ : L Φ) :
(M ⊨[w] (◇ₜ φ)) ↔ ∃ v : M.S, M.R w v ∧ (M ⊨[v] φ) := by
  classical
  simp only [L.dia, L.not, Model.satisfies]
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
$$`M \vDash^m φ \quad\text{iff}\quad
    M,w \vDash φ\text{ for every }w\in M.S.`

We use superscripts on the turnstile to make the level of the
semantics explicit: `m` for models, `f` for frames, and `c` for
classes of frames. Replacing `⊨` with `⊭` negates each relation.

```lean
@[simp]
def L.true_in_model (M : @Model Φ) (φ : L Φ) : Prop :=
  ∀ w : M.S, M ⊨[w] φ

infixl:51 " ⊨ᵐ " => L.true_in_model
notation M " ⊭ᵐ " φ => ¬ L.true_in_model M φ
```

A formula φ is valid in a frame F if it is true in every model based on F.
$$`F \vDash^f φ \quad\text{iff}\quad
    M \vDash^m φ\text{ for every model }M\text{ based on }F.`
```lean
@[simp]
def L.valid_in_frame (F : Frame) (φ : L Φ) : Prop :=
  ∀ M : @Model Φ, M.toFrame = F → M ⊨ᵐ φ

infixl:51 " ⊨ᶠ " => L.valid_in_frame
notation F " ⊭ᶠ " φ => ¬ L.valid_in_frame F φ
```

A formula φ is valid in a class of frames C if it is valid in every frame in C.
$$`C \vDash^c φ \quad\text{iff}\quad
    F \vDash^f φ\text{ for every }F\in C.`
In Lean we represent a class as a set of frames.
```lean
@[simp]
def L.valid_in_class (C : Set Frame) (φ : L Φ) : Prop :=
  ∀ F : Frame, F ∈ C → F ⊨ᶠ φ

infixl:51 " ⊨ᶜ " => L.valid_in_class
notation C " ⊭ᶜ " φ => ¬ L.valid_in_class C φ
```

We say a formula *is valid* if it is true in all models,
or equivalently, valid in the class of all frames.
```lean
@[simp]
def L.valid (φ : L Φ) : Prop :=
  ∀ M : @Model Φ, M ⊨ᵐ φ
prefix:max "⊨ " => L.valid
notation "⊭ " φ => ¬ L.valid φ

theorem L.valid_iff_valid_in_class (φ : L Φ) :
(⊨ φ) ↔ Set.univ ⊨ᶜ φ := by
  simp only [valid, true_in_model, valid_in_class,
    Set.mem_univ, valid_in_frame, forall_const]
  apply Iff.intro
  · intro a F M a_1 w
    subst a_1
    simp_all only
  · intro a M w
    simp_all only
```


We have analogous definitions for truth and validity over schemas.
A schema is true in a model if every instance of the schema is
true in the model. We define these such that the
`[]ₛ` notation is implicity when using the `⊨ˢ` notations.

```lean
@[simp]
def Schema.true_in_model [DecidableEq Φ] (Γ : L Φ) (M : @Model Φ) : Prop :=
  ∀ φ ∈ [Γ]ₛ, M ⊨ᵐ φ
notation M " ⊨ᵐˢ " Γ => Schema.true_in_model Γ M
notation M " ⊭ᵐˢ " Γ => ¬ Schema.true_in_model Γ M

@[simp]
def Schema.valid_in_frame [DecidableEq Φ] (Γ : L Φ) (F : Frame) : Prop :=
  ∀ M : @Model Φ, M.toFrame = F → M ⊨ᵐˢ Γ
notation F " ⊨ᶠˢ " Γ => Schema.valid_in_frame Γ F
notation F " ⊭ᶠˢ " Γ => ¬ Schema.valid_in_frame Γ F

@[simp]
def Schema.valid_in_class [DecidableEq Φ] (Γ : L Φ) (C : Set Frame) : Prop :=
  ∀ F : Frame, F ∈ C → F ⊨ᶠˢ Γ
notation C " ⊨ᶜˢ " Γ => Schema.valid_in_class Γ C
notation C " ⊭ᶜˢ " Γ => ¬ Schema.valid_in_class Γ C

@[simp]
def Schema.valid [DecidableEq Φ] (Γ : L Φ) : Prop :=
  ∀ M : @Model Φ, M ⊨ᵐˢ Γ
prefix:max "⊨ˢ " => Schema.valid
notation "⊭ˢ " Γ => ¬ Schema.valid Γ

```
:::


We can show a formula is not valid by providing a countermodel, i.e. a model
in which the formula is not true. Similarly we can show a schema is not
valid by providing a countermodel in which some instance of the schema
is not true, or by directly providing a countermodel and a counterinstance
of the schema.
```lean
@[simp]
theorem not_valid_iff_countermodel {φ : L Φ} :
(⊭ φ) ↔ ∃ M : @Model Φ, M ⊭ᵐ φ := by
  simp only [L.valid, L.true_in_model, not_forall]

@[simp]
theorem schema_not_valid_iff_countermodel [DecidableEq Φ] {Γ : L Φ} :
(⊭ˢ Γ) ↔ ∃ M : @Model Φ, M ⊭ᵐˢ Γ := by
  simp only [Schema.valid, Schema.true_in_model, not_forall]

@[simp]
theorem schema_not_valid_iff_countermodel_and_counterinstance
[DecidableEq Φ] {Γ : L Φ} :
(⊭ˢ Γ) ↔ ∃ M : @Model Φ, ∃ φ ∈ [Γ]ₛ, M ⊭ᵐ φ := by
  simp

theorem schema_not_valid_of_not_valid
[DecidableEq Φ] {Γ : L Φ} (h : ⊭ Γ) : ⊭ˢ Γ := by
  apply schema_not_valid_iff_countermodel_and_counterinstance.mpr
  rcases not_valid_iff_countermodel.mp h with ⟨M, hM⟩
  exact ⟨M, Γ, L.mem_schema_self Γ, hM⟩
```

*Exercises*

1) Show that the following schema are true in all models,
   hence valid in all frames.
* $`□⊤`
* $`□(φ → ψ) → (□φ → □ψ)`
* $`◇(φ → ψ) → (□φ → ◇ψ)`
* $`□(φ → ψ) → (◇φ → ◇ψ)`
* $`□(φ ∧ ψ) ↔ (□φ ∧ □ψ)`
* $`◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)`

:::details "Solutions"
The denumerability of `Φ` gives us an enumeration of its atoms.
We call its first two atoms `φ` and `ψ`. After choosing an arbitrary
instance of a schema, its substitution `σ` turns these placeholders
into arbitrary formulas.

```lean
variable [Denumerable Φ]

local notation "φ₀" => Denumerable.ofNat Φ 0
local notation "ψ₀" => Denumerable.ofNat Φ 1
local notation "φ" => L.atom φ₀
local notation "ψ" => L.atom ψ₀

example : ⊨ˢ (□ₜ⊤ₜ : L Φ) := by
  change ∀ M : @Model Φ, ∀ x ∈ [□ₜ⊤ₜ]ₛ, M ⊨ᵐ x
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  intro w v _ h2
  exact h2

example : ⊨ˢ (□ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ □ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  intro w hbox hφ v hv
  exact hbox v hv (hφ v hv)

example : ⊨ˢ (◇ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ ◇ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  intro w hdia hbox
  rcases (M.satisfies_dia w _).mp hdia with
    ⟨v, hv, himp⟩
  exact (M.satisfies_dia w _).mpr
    ⟨v, hv, himp (hbox v hv)⟩

example : ⊨ˢ (□ₜ(φ →ₜ ψ) →ₜ (◇ₜφ →ₜ ◇ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  intro w hbox hdia
  rcases (M.satisfies_dia w _).mp hdia with
    ⟨v, hv, hφ⟩
  exact (M.satisfies_dia w _).mpr
    ⟨v, hv, hbox v hv hφ⟩

example : ⊨ˢ (□ₜ(φ ∧ₜ ψ) ↔ₜ (□ₜφ ∧ₜ □ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  change M ⊨ᵐ
    (□ₜ(σ φ₀ ∧ₜ σ ψ₀) ↔ₜ
      (□ₜ(σ φ₀) ∧ₜ □ₜ(σ ψ₀)))
  intro w
  rw [Model.satisfies_iff, Model.satisfies_and]
  constructor
  · intro h
    constructor
    · intro v hv
      exact (M.satisfies_and v _ _).mp (h v hv) |>.left
    · intro v hv
      exact (M.satisfies_and v _ _).mp (h v hv) |>.right
  · intro h v hv
    exact (M.satisfies_and v _ _).mpr
      ⟨h.left v hv, h.right v hv⟩

example : ⊨ˢ (◇ₜ(φ ∨ₜ ψ) ↔ₜ (◇ₜφ ∨ₜ ◇ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  change M ⊨ᵐ
    (◇ₜ(σ φ₀ ∨ₜ σ ψ₀) ↔ₜ
      (◇ₜ(σ φ₀) ∨ₜ ◇ₜ(σ ψ₀)))
  intro w
  rw [Model.satisfies_iff, Model.satisfies_or]
  apply Iff.intro
  · case mp =>
    intro h
    rcases (M.satisfies_dia w _).mp h with
      ⟨v, hv, hφψ⟩
    cases (M.satisfies_or v _ _).mp hφψ with
    | inl hφ =>
        exact Or.inl ((M.satisfies_dia w _).mpr
          ⟨v, hv, hφ⟩)
    | inr hψ =>
        exact Or.inr ((M.satisfies_dia w _).mpr
          ⟨v, hv, hψ⟩)
  · case mpr =>
    intro h
    cases h with
    | inl hφ =>
      rcases (M.satisfies_dia w _).mp hφ with
        ⟨v, hv, hφv⟩
      exact (M.satisfies_dia w _).mpr
        ⟨v, hv, (M.satisfies_or v _ _).mpr (Or.inl hφv)⟩
    | inr hψ =>
      rcases (M.satisfies_dia w _).mp hψ with
        ⟨v, hv, hψv⟩
      exact (M.satisfies_dia w _).mpr
        ⟨v, hv, (M.satisfies_or v _ _).mpr (Or.inr hψv)⟩
```
:::

2) Show that the following schema do not hold in all frames by
providing a countermodel or counterframe.
* $`□φ → φ`
* $`◇⊤`
* $`□(φ → ψ) → (□φ → ◇ψ)`
* $`◇φ → □φ`
* $`□(□φ → ψ) ∨ □(□ψ → □φ)`
* $`□(φ ∨ ψ) → (□φ ∨ □ψ)`
* $`□(□φ → φ) → □φ`

:::details "Solutions"
In each picture, an arrow from wᵢ to wⱼ means that wⱼ is accessible from wᵢ.The
second line inside each circle lists which of φ, ψ, and χ are true there;
∅ means that none of these atoms is true.

The denumerability of Φ ensures that φ and ψ name distinct atoms.

```lean
theorem schema_atoms_ne : φ₀ ≠ ψ₀ := by
  intro h
  have h' := congrArg (Encodable.encode : Φ → Nat) h
  simpa [Denumerable.encode_ofNat] using h'
```

For $`□φ → φ`, take a one-world dead-end model. It has no accessibility
arrows, and every atom is false at its only world.

```lean
private abbrev deadEndCountermodel : @Model Φ :=
  { S := Fin 1
    R := fun _ _ => False
    V := fun _ _ => False }
```

```diagram (cssWidth := "10em") (texWidth := "10em")
Model.diagram (deadEndCountermodel (Φ := Nat))
```

```lean
example : ⊭ˢ (□ₜφ →ₜ φ) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := deadEndCountermodel
  refine ⟨M, ?_⟩
  intro hAll
  have hp := hAll 0
  exact hp (fun _ hR => False.elim hR)
```

For $`◇⊤`, the countermodel is the same dead-end model.

```diagram (cssWidth := "10em") (texWidth := "10em")
Model.diagram (deadEndCountermodel (Φ := Nat))
```

```lean
example : ⊭ˢ (◇ₜ⊤ₜ : L Φ) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := deadEndCountermodel
  refine ⟨M, ?_⟩
  intro hAll
  have hDia := hAll 0
  rcases (M.satisfies_dia 0 ⊤ₜ).mp hDia with
    ⟨_, hR, _⟩
  exact hR
```

For $`□(φ → ψ) → (□φ → ◇ψ)`, use the dead-end model once more.

```diagram (cssWidth := "10em") (texWidth := "10em")
Model.diagram (deadEndCountermodel (Φ := Nat))
```

```lean
example : ⊭ˢ (□ₜ(φ →ₜ ψ) →ₜ (□ₜφ →ₜ ◇ₜψ)) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := deadEndCountermodel
  refine ⟨M, ?_⟩
  intro hAll
  have h := hAll 0
  have hDia := h
    (fun _ hR => False.elim hR)
    (fun _ hR => False.elim hR)
  rcases (M.satisfies_dia 0 ψ).mp hDia with
    ⟨_, hR, _⟩
  exact hR
```

For $`◇φ → □φ`, use a model where w₀ can access both worlds, including
itself. The atom φ is true at w₁ but false at w₀.

```lean
private abbrev branchCountermodel (p₀ : Φ) : @Model Φ :=
  { S := Fin 2
    R := fun w _ => w = 0
    V := fun p w => p = p₀ ∧ w = 1 }
```

```diagram (cssWidth := "16em") (texWidth := "16em")
Model.diagram (branchCountermodel (Φ := Nat) 0)
```

```lean
example : ⊭ˢ (◇ₜφ →ₜ □ₜφ) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := branchCountermodel φ₀
  refine ⟨M, ?_⟩
  intro hAll
  have h := hAll 0
  have hpDia : M ⊨[0] ◇ₜφ := by
    apply (M.satisfies_dia 0 φ).mpr
    exact ⟨1, rfl, rfl, rfl⟩
  have hpFalse := h hpDia 0 rfl
  exact Fin.zero_ne_one hpFalse.2
```

For the disjunction of boxes, use four worlds. The two branches from w₀ make
different disjuncts fail; the extra successor w₃ of w₂ makes ψ true there but
φ false.

```lean
private abbrev fourWorldCountermodel (q₀ : Φ) : @Model Φ :=
  { S := Fin 4
    R := fun w v =>
      (w = 0 ∧ v = 1) ∨
      (w = 0 ∧ v = 2) ∨
      (w = 2 ∧ v = 3)
    V := fun p w => p = q₀ ∧ w = 3 }
```

```diagram (cssWidth := "28em") (texWidth := "28em")
Model.diagram (fourWorldCountermodel (Φ := Nat) 1)
```

```lean
example : ⊭ˢ (□ₜ(□ₜφ →ₜ ψ) ∨ₜ □ₜ(□ₜψ →ₜ □ₜφ)) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := fourWorldCountermodel ψ₀
  refine ⟨M, ?_⟩
  intro hAll
  have h := (M.satisfies_or 0 _ _).mp (hAll 0)
  cases h with
  | inl hleft =>
      have himp := hleft 1 (Or.inl ⟨rfl, rfl⟩)
      have hpBox : M ⊨[1] □ₜφ := by
        intro v hR
        rcases hR with hR | hR | hR <;> omega
      have hqLeft := himp hpBox
      exact (by decide : (1 : Fin 4) ≠ 3) hqLeft.2
  | inr hright =>
      have himp := hright 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hqBox : M ⊨[2] □ₜψ := by
        intro v hR
        rcases hR with hR | hR | hR
        · omega
        · omega
        · exact ⟨rfl, hR.2⟩
      have hpBox := himp hqBox
      have hpEnd := hpBox 3 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact schema_atoms_ne hpEnd.1
```

For $`□(φ ∨ ψ) → (□φ ∨ □ψ)`, use a model in which every world accessible
from w₀ satisfies at least one of φ and ψ, but neither atom is true at every
accessible world.

```lean
private abbrev splitCountermodel (p₀ q₀ : Φ) : @Model Φ :=
  { S := Fin 2
    R := fun w _ => w = 0
    V := fun p w =>
      (p = p₀ ∧ w = 1) ∨
      (p = q₀ ∧ w = 0) }
```

```diagram (cssWidth := "16em") (texWidth := "16em")
Model.diagram (splitCountermodel (Φ := Nat) 0 1)
```

```lean
example : ⊭ˢ (□ₜ(φ ∨ₜ ψ) →ₜ (□ₜφ ∨ₜ □ₜψ)) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := splitCountermodel φ₀ ψ₀
  refine ⟨M, ?_⟩
  intro hAll
  have h := hAll 0
  have hpqBox : M ⊨[0] □ₜ(φ ∨ₜ ψ) := by
    intro v _
    apply (M.satisfies_or v _ _).mpr
    fin_cases v
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  have hpOrq := (M.satisfies_or 0 _ _).mp (h hpqBox)
  cases hpOrq with
  | inl hpBox =>
      have hpFalse := hpBox 0 rfl
      rcases hpFalse with ⟨_, hfalse⟩ | ⟨hbad, _⟩
      · exact Fin.zero_ne_one hfalse
      · exact schema_atoms_ne hbad
  | inr hqBox =>
      have hqTrue := hqBox 1 rfl
      rcases hqTrue with ⟨hbad, _⟩ | ⟨_, htrue⟩
      · exact schema_atoms_ne hbad.symm
      · exact Fin.zero_ne_one htrue.symm
```

Finally, use a reflexive one-world model for the Löb schema. The atom φ is
false at w₀, and the loop records that w₀ is accessible from itself.

```lean
private abbrev reflexiveCountermodel : @Model Φ :=
  { S := Fin 1
    R := fun _ _ => True
    V := fun _ _ => False }
```

```diagram (cssWidth := "10em") (texWidth := "10em")
Model.diagram (reflexiveCountermodel (Φ := Nat))
```

```lean
example :
    ⊭ˢ (□ₜ(□ₜφ →ₜ φ) →ₜ □ₜφ) := by
  apply schema_not_valid_of_not_valid
  apply not_valid_iff_countermodel.mpr
  let M : @Model Φ := reflexiveCountermodel
  refine ⟨M, ?_⟩
  intro hAll
  have h := hAll 0
  have hAntecedent :
      M ⊨[0] □ₜ(□ₜφ →ₜ φ) := by
    intro v _ hpBox
    exact hpBox 0 trivial
  exact h hAntecedent 0 trivial
```
:::
