import Mathlib
import VersoManual
import Textbook.Blocks

import LOTAC2.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Textbook

#doc (Manual) "Frames and Models" =>

# Frames and Models

:::definition "Frames and Models"

A frame is a pair $`(S, R)` where `S` is a non-empty set of worlds and $R$ is
a binary relation on $`S` called the accessibility relation.

```lean
structure Frame where
  -- The type of worlds
  S : Type
  /-- Require that the set of worlds is non-empty -/
  [S_nonempty : Nonempty S]
  /-- The accessibility relation on worlds -/
  R : S → S → Prop
```

A Φ-model is a pair $`(F, V)` where `F` is a frame and `V` is a _valuation
function_ that assigns worlds and propositional variables to truth values.
I.e a propositional variable $`p` holds at a world $`w` if and only if
$`V(p,w)`$.

In Lean we represent models as an extension of frames with a valuation function.
{margin}[This lets us use `M.S` and `M.R` from the frame, rather than needing to
write `M.F.S` and `M.F.R`, if we used the frame directly in the structure.]
```lean
variable {Φ : Type}

structure Model extends Frame where
  V : Φ → S → Prop

```

```lean -show

--The following code is used to render finite models as diagrams.
--It is not part of the formalization, but extremely useful for visualization.
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
Let $`M = (S, R, V)` be a Φ-model and let $`w` be a world in `S`.
We define the satisfaction relation $`M \vDash_w φ` for a formula `φ`
inductively as follows.
$$`
\begin{aligned}
M \vDash_w p &\quad\text{iff}\quad V(p, w)\\
M \vDash_w ⊥ &\quad\text{iff}\quad \text{False}\\
M \vDash_w φ → ψ &\quad\text{iff}\quad M \vDash_w φ \rightarrow M \vDash_w ψ\\
M \vDash_w □φ &\quad\text{iff}\quad \forall v, R(w, v) \rightarrow M \vDash_v φ
\end{aligned}
`

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

Satisfaction extends to the other logical connectives based on their
definitions. Note that these themselves are not definitions, but are theorems
that follow from the definition of satisfaction and the definitions of the
logical connectives.
$$`
\begin{aligned}
M \vDash_w ¬φ &\quad\text{iff}\quad M \nvDash_w φ\\
M \vDash_w φ ∧ ψ &\quad\text{iff}\quad M \vDash_w φ \wedge M \vDash_w ψ\\
M \vDash_w φ ∨ ψ &\quad\text{iff}\quad M \vDash_w φ \vee M \vDash_w ψ\\
M \vDash_w φ ↔ ψ &\quad\text{iff}\quad M \vDash_w φ \leftrightarrow M \vDash_w ψ\\
M \vDash_w ◇φ &\quad\text{iff}\quad \exists v, R(w, v) \wedge M \vDash_v φ
\end{aligned}
`

```lean
theorem Model.satisfies_neg (M : @Model Φ) (w : M.S) (φ : L Φ) :
(M ⊨[w] ¬ₜφ) ↔ (M ⊭[w] φ) := by
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




:::definition "Truth and Validity"

A formula φ is true in a model M if it is satisfied at every world in M.
$$`M \vDash^m φ \quad\text{iff}\quad \forall w, M \vDash_w φ`

We use superscripts on the turnstile to make the level of the
semantics explicit: `m` for models, `f` for frames, and `c` for
classes of frames. Replacing `⊨` with `⊭` negates each relation.

```lean
@[simp]
def L.true_in_model (M : @Model Φ) (φ : L Φ) : Prop :=
  ∀ w, M ⊨[w] φ

infixl:51 " ⊨ᵐ " => L.true_in_model
notation M " ⊭ᵐ " φ => ¬ L.true_in_model M φ
```

A formula φ is valid in a frame F if it is true in every model based on F.
$$`F \vDash^f φ := ∀ V, (F, V) \vDash^m φ`
```lean
@[simp]
def L.valid_in_frame (F : Frame) (φ : L Φ) : Prop :=
  ∀ V, (Model.mk F V) ⊨ᵐ φ

infixl:51 " ⊨ᶠ " => L.valid_in_frame
notation F " ⊭ᶠ " φ => ¬ L.valid_in_frame F φ
```

A formula φ is valid in a class of frames C if it is valid in every frame in C.
$$`C \vDash^c φ := ∀ F ∈ C, F \vDash^f φ`
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
  · intro a F V w
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

1) Show that the following schema are true in all models.
$$`
\begin{aligned}
□⊤ & \\
□(φ → ψ) → (□φ → □ψ) & \text{(the K axiom)} \\
◇(φ → ψ) → (□φ → ◇ψ) & \\
□(φ → ψ) → (◇φ → ◇ψ) & \\
□(φ ∧ ψ) ↔ (□φ ∧ □ψ) & \\
◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ) & \\
\end{aligned}`

:::details "Solutions"
The denumerability of `Φ` gives us an enumeration of its atoms.
We call its first two atoms `φ` and `ψ`. After choosing an arbitrary
instance of a schema, its substitution `σ` turns these placeholders
into arbitrary formulas.

```lean
section Examples

variable [Denumerable Φ]

local notation "φ₀" => Denumerable.ofNat Φ 0
local notation "ψ₀" => Denumerable.ofNat Φ 1
local notation "φ" => L.atom φ₀
local notation "ψ" => L.atom ψ₀

example : ⊨ˢ (□ₜ⊤ₜ : L Φ) := by
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
  rcases (M.satisfies_dia w _).mp hdia with ⟨v, hv, himp⟩
  exact (M.satisfies_dia w _).mpr ⟨v, hv, himp (hbox v hv)⟩

example : ⊨ˢ (□ₜ(φ →ₜ ψ) →ₜ (◇ₜφ →ₜ ◇ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  intro w hbox hdia
  rcases (M.satisfies_dia w _).mp hdia with ⟨v, hv, hφ⟩
  exact (M.satisfies_dia w _).mpr ⟨v, hv, hbox v hv hφ⟩

example : ⊨ˢ (□ₜ(φ ∧ₜ ψ) ↔ₜ (□ₜφ ∧ₜ □ₜψ)) := by
  intro M χ hχ
  rcases hχ with ⟨σ, rfl⟩
  change M ⊨ᵐ (□ₜ(σ φ₀ ∧ₜ σ ψ₀) ↔ₜ (□ₜ(σ φ₀) ∧ₜ □ₜ(σ ψ₀)))
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
  change M ⊨ᵐ (◇ₜ(σ φ₀ ∨ₜ σ ψ₀) ↔ₜ (◇ₜ(σ φ₀) ∨ₜ ◇ₜ(σ ψ₀)))
  intro w
  rw [Model.satisfies_iff, Model.satisfies_or]
  apply Iff.intro
  · case mp =>
    intro h
    rcases (M.satisfies_dia w _).mp h with ⟨v, hv, hφψ⟩
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
providing a countermodel or counterframe. Some of these formulae are famous
named axioms, which we will study in later chapters.
$$`
\begin{aligned}
□φ → φ & \text{(the T axiom)} \\
◇⊤ & \text{(variant of the D axiom)} \\
□(φ → ψ) → (□φ → ◇ψ) & \\
◇φ → □φ & \text{(Brouwer's axiom / the 5 axiom)} \\
□(□φ → ψ) ∨ □(□ψ → □φ) &  \\
□(φ ∨ ψ) → (□φ ∨ □ψ) & \\
□(□φ → φ) → □φ & \text{(Löb's axiom)}
\end{aligned}`

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
example : ⊭ˢ (□ₜ(□ₜφ →ₜ φ) →ₜ □ₜφ) := by
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

3) Show that $`◇⊤` and schema $`□φ → ◇φ` share the same models. i.e
$`∀ M, (M ⊨ᵐ ◇⊤) ↔ (M ⊨ᵐˢ □φ → ◇φ)` {margin}[In other words, these are two
different ways of expressing the same property of models, or as we will see later,
equivalent ways of writing the D axiom.]

:::details "Solution"
```lean
example : ∀ M : @Model Φ, (M ⊨ᵐ ◇ₜ⊤ₜ) ↔ (M ⊨ᵐˢ (□ₜφ →ₜ ◇ₜφ)) := by
  sorry
```
:::

4) Exhibit a frame that validates □⊥. i.e., prove $`∃ F, F ⊨ᶠ □⊥`.
:::details "Solution"
```lean
example : ∃ F, F ⊨ᶠ (□ₜ⊥ₜ : L Φ) := by
  sorry
```
:::

5) Show the following. (1) If a formula is a tautology, it holds in any model
(i.e. it is valid, $`M ⊨ᵐ φ` for all $`M`) . (2) If $`M ⊨ᵐ φ → ψ` and $`M ⊨ᵐ φ`
then $`M ⊨ᵐ ψ`. (3) if $`M ⊨ᵐ φ` then $`M ⊨ᵐ □φ`.
```lean
example : ∀ M : @Model Φ, (⊨ φ) → (M ⊨ᵐ φ) := by
  sorry

example : ∀ M : @Model Φ, (M ⊨ᵐ (φ →ₜ ψ)) ∧ (M ⊨ᵐ φ) → (M ⊨ᵐ ψ) := by
  sorry

example : ∀ M : @Model Φ, (M ⊨ᵐ φ) → (M ⊨ᵐ □ₜφ) := by
  sorry
```

6) Show that the above hold for frames as well. i.e.
(1) If a formula is a tautology, it holds in any frame,
(2) If $`F ⊨ᶠ φ → ψ` and $`F ⊨ᶠ φ` then $`F ⊨ᶠ ψ`.
(3) if $`F ⊨ᶠ φ` then $`F ⊨ᶠ □φ`.
```lean
example : ∀ F : Frame, (⊨ φ) → (F ⊨ᶠ φ) := by
  sorry

example : ∀ F : Frame, (F ⊨ᶠ (φ →ₜ ψ)) ∧ (F ⊨ᶠ φ) → (F ⊨ᶠ ψ) := by
  sorry

example : ∀ F : Frame, (F ⊨ᶠ φ) → (F ⊨ᶠ □ₜφ) := by
  sorry

end Examples
```

# Ancestral and Descendant Worlds

Given a frame $`F = (S, R)` and a world $`w \in S`, we define the
reflexive transitive closure of $`R` as follows. We begin by defining the
$`n`-step accessibility relation $`R^n` for each natural number $`n`.
$$`
R^0(w, v) \quad\text{iff}\quad w = v
R^{n+1}(w, v) \quad\text{iff}\quad R(w, v) \vee \exists u, R(w, u) \wedge R^n(u, v)
`

```lean
@[simp]
def Frame.R_n (F : Frame) : Nat → F.S → F.S → Prop
| 0, w, v => w = v
| n+1, w, v => F.R w v ∨ ∃ u, F.R w u ∧ Frame.R_n F n u v
```
From this we define the reflexive transitive closure $`R^*` as existance
of an $`n` such that $`R^n(w, v)` holds.

```lean
@[simp]
def Frame.R_Star (F : Frame) (w v : F.S) : Prop :=
  ∃ n, Frame.R_n F n w v
```

## Exercises

1) R^1 = R. Show that for any frame F, any world w, and any world v, we have
$`R^1(w, v) \quad\text{iff}\quad R(w, v)`
2) if $`R^*(w, v)` holds, then there exists a sequence of worlds
$`w_0, w_1, \dots, w_n` (with $`w_0 = w` and $`w_n = v`) such that
for all $`i < n, R(w_i, w_{i+1})` holds.
3) $`R^*` is reflexive and transitive.
4) Let $`T` be any transitive relation on the set of worlds $`S`.
Show that if $`R \subseteq T`, then $`R^* \subseteq T`. i.e $`R^*` is the
smallest reflexive and transitive relation on $`S` containing $`R`.
5) If $`S = ℤ` and $`R = {(w, w+1) | w ∈ S}`, what is $`R^*`? Provide the
relation `Q : ℤ → ℤ → Prop` and show that $`R^* = Q`.

```lean
theorem Frame.R_n.R_1_eq_R (F : Frame) (w v : F.S) : F.R_n 1 w v ↔ F.R w v := by
  simp only [R_n, exists_eq_right, or_self]

theorem Frame.R_Star.exists_sequence (F : Frame) (w v : F.S) :
F.R_Star w v ↔ ∃ n : Nat, ∃ (w_seq : Fin (n+1) → F.S),
  w_seq 0 = w ∧ w_seq ⟨n, by simp⟩ = v ∧
  ∀ i : Fin n, F.R (w_seq ⟨i.1, by simp⟩) (w_seq ⟨i.1 + 1, by simp⟩) := by
  sorry

@[simp]
theorem Frame.R_Star.refl (F : Frame) (w : F.S) : F.R_Star w w := by
  simp only [R_Star]
  exact ⟨0, rfl⟩

theorem Frame.R_Star.trans (F : Frame) (w u v : F.S) :
F.R_Star w u → F.R_Star u v → F.R_Star w v := by
  simp
  intro n H1 m H2
  sorry
```


# Generated Submodels

Given the previously defined reflexive transitive closure of the
accessibility relation, we can define the submodel generated by a world
in a model.

Intuitively, the submodel generated by a world $`w`$ consists of all worlds
that are accessible from $`w`$ (including $`w`$ itself), along with the
restriction of the accessibility relation and valuation to these worlds.

:::definition "Generated Submodel"
Given a model $`M = (S, R, V)` and a world $`w \in S`, we define the _submodel
 of $`M` generated by $`w`_ as the model $`M_w = (S_w, R_w, V_w)` where
- $`S_w = {v ∈ S | R^*(w, v)}` is the set of worlds accessible from $`w`
(including $`w` itself),
- $`R_w = R \cap (S_w \times S_w)` is the restriction of $`R` to $`S_w`,
- $`V_w(p) = V(p) \cap S_w` for each propositional variable $`p`.

```lean

-- The type of worlds accessible from a given world w in a frame F.
abbrev Frame.S_sub (F : Frame) (w : F.S) : Type :=
  {u : F.S // F.R_Star w u}

abbrev Frame.R_sub (F : Frame) (w : F.S) (u v : F.S_sub w) : Prop :=
  F.R u v

abbrev Model.V_sub (M : @Model Φ) (w : M.S) (p : Φ) (v : M.S_sub w) : Prop :=
  M.V p v

def Frame.subframe (F : Frame) (w : F.S) : Frame := {
  S := F.S_sub w,
  -- S is nonempty because w is in S and R^* is reflexive
  S_nonempty := by exists w; apply Frame.R_Star.refl
  R := F.R_sub w
}

def Model.submodel (M : @Model Φ) (w : M.S) : @Model Φ := {
  toFrame := M.subframe w,
  V := M.V_sub w
}

```

:::

:::theorem "The Submodel Lemma"
For any model $`M = (S, R, V)`, any $`w \in S`, and any world $`v \in S_w`
We have that $`M_w ⊨_v φ` if and only if $`M ⊨_v φ`.
```lean
theorem Model.submodel_lemma
(M : @Model Φ) {φ : L Φ} {w : M.S} {v : M.S_sub w} :
(M.submodel w ⊨[v] φ) ↔ M ⊨[v] φ := by
  induction φ generalizing v
  . case atom p =>
    simp_all only [satisfies, Frame.R_Star]
    obtain ⟨val, property⟩ := v
    simp_all only [Frame.R_Star]
    rfl
  . case bot =>
    simp_all only [satisfies]
  . case imp φ ψ ihφ ihψ =>
    simp_all only [satisfies]
  . case box φ ih =>
    constructor
    · intro h u hvu
      have hu : M.R_Star w u := by
        exact Frame.R_Star.trans M.toFrame w v u v.2 ⟨1, Or.inl hvu⟩
      exact (@ih ⟨u, hu⟩).mp (h ⟨u, hu⟩ hvu)
    · intro h u hvu
      exact (@ih u).mpr (h u.1 hvu)
```

From this we get three corolaries:
1) If a formula is true in a model, then it is true in any submodel.
$$`M ⊨ᵐ φ \implies M_w ⊨ᵐ φ`
2) A formula is true in a model iff it is true in all of its submodels.
$$`M ⊨ᵐ φ \iff ∀w, M_w ⊨ᵐ φ`
3) A formula is valid in a frame iff it is valid in all of its subframes.
$$`F ⊨ᶠ φ \iff ∀w, F_w ⊨ᶠ φ`
```lean

lemma Model.submodel_satisfies_from_satisfies
(M : @Model Φ) {φ : L Φ} {w : M.S} :
(M ⊨ᵐ φ) → (M.submodel w ⊨ᵐ φ) := by
  intro h v
  exact M.submodel_lemma.mpr (h v.1)

lemma Model.satisfies_iff_all_submodel_satisfies
(M : @Model Φ) {φ : L Φ} :
(M ⊨ᵐ φ) ↔ ∀w, M.submodel w ⊨ᵐ φ := by
  constructor
  · intro h w
    exact M.submodel_satisfies_from_satisfies h
  · intro h v
    have h' := h v
    simp at h'
    have h'' := h' ⟨v, by apply Frame.R_Star.refl⟩
    exact M.submodel_lemma.mp h''

lemma Frame.valid_iff_all_subframe_valid
(F : Frame) {φ : L Φ} :
(F ⊨ᶠ φ) ↔ ∀w, F.subframe w ⊨ᶠ φ := by
  simp only [L.valid_in_frame]
  constructor
  · intro h w M hM
    sorry
  . intro h M hM
    sorry
```
:::

# P-morphisms

:::definition "p-Morphisms"
Let $`M_1 = (S_1, R_1, V_1)` and $`M_2 = (S_2, R_2, V_2)`.
A function $`f:S_1 → S_2` satisfying the following three
conditions is called a _p-morphism_ from $`M_1` to $`M_2`.
$$`
\begin{aligned}
R_1(s,t) &→ R_2(f(s), f(t)) \\
R_2(f(s), u) &→ ∃t, R_1(s,t) ∧ f(t) = u \\
V_1(p, s) \iff V_2(p, f(s))
\end{aligned}
`
A function satisfying only the first two conditions is said to be
a p-morphism on frames.
```lean

class pMorphismF {F1 F2 : Frame} (f : F1.S → F2.S) : Prop where
  c1 {s t : F1.S} : F1.R s t → F2.R (f s) (f t)
  c2 {s : F1.S} {u : F2.S} : F2.R (f s) u → ∃t, F1.R s t ∧ f t = u

class pMorphism {M1 M2 : @Model Φ} (f : M1.S → M2.S) : Prop
extends pMorphismF f where
  c3 {p : Φ} {s : M1.S} : M1.V p s ↔ M2.V p (f s)
```
:::


:::theorem "p-Morphism Lemma"

For any formula $`φ`, two models $`M_1, M_2`, world $`w ∈ S_1`
and p-Morphism between them $`f`,
we have that $$`M_1 ⊨_w φ ↔ M_2 ⊨_{f(w)} φ`

```lean
theorem pMorphism.satisfies_iff
{M1 M2 : @Model Φ} {f : M1.S → M2.S} [pMorphism f] {φ : L Φ} {w : M1.S} :
(M1 ⊨[w] φ) ↔ (M2 ⊨[f w] φ) := by
  induction φ generalizing w
  . case atom p =>
    simp_all only [Model.satisfies]
    apply Iff.intro
    · intro a
      apply pMorphism.c3.mp a
    · intro a
      apply pMorphism.c3.mpr a
  . case bot =>
    simp_all only [Model.satisfies]
  . case imp a1 a2 ih1 ih2 =>
    simp_all only [Model.satisfies]
  . case box a1 ih =>
    simp_all only [Model.satisfies]
    apply Iff.intro
    · intro a v a_1
      have ⟨_, hw⟩ := pMorphismF.c2 a_1
      obtain ⟨left, right⟩ := hw
      subst right
      simp_all only
    · intro a v a_1
      apply a
      exact pMorphismF.c1 a_1
```

:::

:::definition "p-Morphic Image"
For two frames $`F_1` and $`F_2` we say $`F_1` is the _p-morphic image_ of
$`F_2` if there exists a surjective p-morphism $`f` between them.

```lean
@[simp]
def pMorphicImage (F1 F2 : Frame) : Prop :=
∃ (f : F1.S → F2.S), pMorphismF f ∧ Function.Surjective f
```
:::

This then leads us to the following

:::theorem "p-Morphism Lemma 2"

If $`F_2` is a p-morphic image of $`F_1` then for any formula $`f`
$$`(F_1 ⊨ᶠ φ) → (F_2 ⊨ᶠ φ)`

```lean
-- TODO: rename
theorem p_morphism_lemma_2 {F1 F2 : Frame} {H : pMorphicImage F1 F2} {φ : L φ}:
F1 ⊨ᶠ φ → F2 ⊨ᶠ φ :=
  sorry
```
:::

## Exercises

Given the follwing two frames $`F1 := ({0, 1}, λxy.\texttt{True})` and
$`F2 := ({0}, λxy.\texttt{True})` show that
$$`
\begin{aligned}
(F_1 ⊨ᶠ φ) &→ (F_2 ⊨ᶠ φ) \\
((ℕ, <) ⊨ᶠ φ) &→ (F_1 ⊨ᶠ φ) \\
\end{aligned}
`

:::details "Solutions"
Both follow directly from our lemma.
We can prove both of these by showing that $`F2` is the p-morphic image
of $`F1` and $`F1` is the $`F1` is the p-morphic image of (ℕ, <). We do this
by providing an explicit p-morphism.
```lean
--TODO: I speed ran this proof and it needs cleanup
example : (⟨Fin 2, λ _ _ => True⟩ ⊨ᶠ φ) → (⟨Fin 1, λ _ _ => True⟩ ⊨ᶠ φ) := by
  apply p_morphism_lemma_2
  exists (λ _ => 0)
  constructor
  constructor
  simp;
  intro s u a
  simp_all only [true_and, exists_const]
  ext : 1
  simp_all only [Fin.val_eq_zero]
  simp [Function.Surjective]

example : (⟨ℕ, (· < ·)⟩ ⊨ᶠ φ) → (⟨Fin 2, λ _ _ => True⟩ ⊨ᶠ φ) := by
  apply p_morphism_lemma_2
  -- Bad selection of F
  exists (λ n => match n with | 0 => 0 | n + 1 => 2)
  constructor
  . case left =>
    constructor
    . case c1 =>
      intro s t a
      simp_all only
    . case c2 => sorry
  . case right =>
    simp [Function.Surjective]
    constructor
    . case left => exists 0
    . case right => sorry
```
:::

# Frame Conditions

TODO, most important section

# Proof Theory

:::definition "Logic"
Given a denumerable set of atomic formulae $`Φ`, a logic is any subset
$`Λ ⊆ Fma(\Φ)` such that:
1) $`Λ` includes all tautologies
2) $`Λ` is closed under _the rule of detachment_ i.e
  $$`φ ∈ Λ, φ → ψ ∈ Λ \implies ψ ∈ Λ`

```lean
class Logic [Denumerable Φ] (Λ : Set (L Φ)) : Prop where
  all_tauto {φ : L Φ} : φ.isTautology → φ ∈ Λ
  detachment {φ ψ : L Φ} : φ ∈ Λ ∧ (φ →ₜ ψ) ∈ Λ → ψ ∈ Λ
```
:::

Some examples of logics are
1) The set of all tautologies, which we call $`PL`.
2) For any class of frames $`C`, the set of all formulae valid in all frames in $`C`
3) The set of all formulae itself.
4) The intersection of any collection of logics $`\{Λ_i | i ∈ I\}`.
  $$`\bigcap_{i ∈ I} Λ_i`

```lean
theorem Logic.intersection [Denumerable Φ] (Λ : I → Set (L Φ))
[∀ i, Logic (Λ i)] :
  Logic (⋂ i, Λ i) := by
  sorry
```


Since the intersection of any collection of logics is itself a logic, we can
define the _smallest logic_ containing a set of formulae $`Γ`$ as the
intersection of all logics containing $`Γ`$.


:::definition "Smallest Logic"
Given a set of formulae $`Γ ⊆ Fma(Φ)`$, the _smallest logic_ containing
$`Γ`$ is the intersection of all logics containing $`Γ`$.

From this, we note that PL is the smallest logic, and FBA is the largest,
in the sense that any logic $`Λ` satisfies $`PL ⊆ Λ ⊆ FBA`.
```lean
lemma Logic.PL_subset [Denumerable Φ] (Λ : Set (L Φ)) [Logic Λ] : PL ⊆ Λ := by
  intro φ h
  sorry

```

:::
