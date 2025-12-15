
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import LOTAC.Formula

variable {Φ : Type} [BEq Φ] [DecidableEq Φ]

set_option linter.unusedSectionVars false

-- Frame
structure F where
  S : Type
  R : S → S → Bool

-- Model
structure M extends F where
  V : Φ → S → Bool

@[simp]
def holds (m : @M Φ) (s : m.S) : @L Φ -> Prop
| .atom p => m.V p s
| ⊥ₜ => False
| A →ₜ B => holds m s A → holds m s B
| □ₜA => ∀ t : m.S, m.R s t → holds m t A

notation m " ⊨[" s "] " A => holds m s A
notation m " ⊭[" s "] " A => ¬holds m s A

@[simp]
theorem holds_not (m : @M Φ) (s : m.S) (A : @L Φ) :
(m ⊨[s] ¬ₜA) ↔ (m ⊭[s] A) := by
  simp only [L.not, holds, imp_false]

@[simp]
theorem holds_top (m : @M Φ) (s : m.S) :
(m ⊨[s] ⊤ₜ) := by
  simp only [L.top, L.not, holds, imp_self]

@[simp]
theorem holds_or (m : @M Φ) (s : m.S) (A B : @L Φ) :
(m ⊨[s] (A ∨ₜ B)) ↔ (m ⊨[s] A) ∨ (m ⊨[s] B) := by
  simp only [L.or, L.not, holds, imp_false]
  apply Iff.intro <;> grind only

@[simp]
theorem holds_and (m : @M Φ) (s : m.S) (A B : @L Φ) :
(m ⊨[s] (A ∧ₜ B)) ↔ (m ⊨[s] A) ∧ (m ⊨[s] B) := by
  simp only [L.and, L.not, holds, imp_false]
  apply Iff.intro <;> grind only

@[simp]
theorem holds_iff (m : @M Φ) (s : m.S) (A B : @L Φ) :
(m ⊨[s] (A ↔ₜ B)) ↔ ((m ⊨[s] A) ↔ (m ⊨[s] B)) := by
  simp only [L.iff, holds_and, holds]
  apply Iff.intro <;> grind only [cases Or]

@[simp]
theorem holds_dia (m : @M Φ) (s : m.S) (A : @L Φ) :
(m ⊨[s] (◇ₜA)) ↔ ∃ t : m.S, m.R s t ∧ (m ⊨[t] A) := by
  simp only [L.dia, L.not, holds, imp_false]
  apply Iff.intro <;> grind only


-- -- Any tautology is a substitution instance of a propositional tautology
-- example (A: @L Φ) (TA : A.tautology):
-- ∃ (B : @L Φ), B.tautology ∧ B.propositional ∧ subst_inst B A := by
--   let b := Sq A


  -- induction A with
  -- | atom p =>
  --   use .atom p
  --   constructor
  --   assumption
  --   constructor
  --   simp only [L.propositional, L.containsBox, decide_false, Bool.false_eq_true, not_false_eq_true,
  --     decide_true]
  --   simp only [subst_inst]
  --   use []
  --   simp only [msubst]
  -- | bot =>
  --   simp only [L.tautology, Lq, L.quasiAtomic, L.isAtomic, L.isBox, V, decide_false,
  --     Bool.false_eq_true, forall_const] at TA
  -- | imp A B ih1 ih2 =>
  --   exists (A →ₜ B)
  --   constructor
  --   exact TA
  --   constructor
  --   sorry
  --   sorry
  -- | box A ih =>



-- A formula is true in a model if it holds at all states in that model
@[simp]
def M.true (m : @M Φ) (A : @L Φ): Prop :=
  ∀ s : m.S, m ⊨[s] A
infix:50 " ⊨ₘ " => M.true

-- A formula is true in all models
@[simp]
def M.trueAll (A : @L Φ) : Prop :=
  ∀ (m : @M Φ), m ⊨ₘ A
prefix:max " ⊨ₘ " => M.trueAll

-- Validity in a frame
-- A formula is valid in a frame if it is true in all models based on that frame
@[simp]
def F.valid (f : F) (A : @L Φ): Prop :=
  ∀ v, (M.mk f v) ⊨ₘ A
infix:50 "⊨" => F.valid

-- A formula is valid in all frames
@[simp]
def F.validAll (A : @L Φ) : Prop :=
  ∀ (f : F), f ⊨ A
prefix:max "⊨" => F.validAll

@[simp]
theorem validAll_iff_trueAll (A : @L Φ) :
(⊨ A) ↔ (⊨ₘ A) := by
  apply Iff.intro
  · intro h m
    apply h m.toF
  · intro h f v
    apply h (M.mk f v)

-- Exercises 1.4

-- 1.4.1
example: ⊨ (□ₜ⊤ₜ : @L Φ) := by
  simp only [F.validAll, F.valid, M.true, holds, L.top, L.not, imp_self, implies_true]

-- K axiom
example (A B : @L Φ) : ⊨ (□ₜ(A →ₜ B) →ₜ (□ₜA →ₜ □ₜB)) := by
  simp only [F.validAll, F.valid, M.true, holds]
  grind only

example (A B : @L Φ) : ⊨ (◇ₜ(A →ₜ B) →ₜ (□ₜA →ₜ ◇ₜB)) := by
  simp
  grind only

example (A B : @L Φ) : ⊨ (□ₜ(A →ₜ B) →ₜ (◇ₜA →ₜ ◇ₜB)) := by
  simp only [F.validAll, F.valid, M.true, holds, L.dia, L.not, imp_false, Classical.not_forall,
    Classical.not_not, forall_exists_index]
  grind only

example (A B : @L Φ) : ⊨ (□ₜ(A ∧ₜ B) →ₜ (□ₜA ∧ₜ □ₜB)) := by
  simp
  grind only

example (A B : @L Φ) : ⊨ (◇ₜ(A ∨ₜ B) →ₜ (◇ₜA ∨ₜ ◇ₜB)) := by
  simp
  grind only


-- Exhibit a frame in which □⊥ is valid
-- The frame with one point and no accessible worlds
-- example : ⟨Fin 1, λ _ _ => False⟩ ⊨ (□ₜ⊥ₜ : @L Φ) := by
--   simp only [F.valid, M.true, holds, imp_self, implies_true]
