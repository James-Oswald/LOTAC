
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import LOTAC.Formula

set_option linter.unusedSectionVars false

-- Frame
structure F where
  S : Type
  R : S → S → Bool

-- Model
structure M extends F where
  V : Nat → S → Bool

@[simp]
def holds (m : M) (s : m.S) : L -> Prop
| .atom p => m.V p s
| ⊥ₜ => False
| A →ₜ B => holds m s A → holds m s B
| □ₜA => ∀ t : m.S, m.R s t → holds m t A

notation m " ⊨[" s "] " A => holds m s A
notation m " ⊭[" s "] " A => ¬holds m s A

@[simp]
theorem holds_not (m : M) (s : m.S) (A : L) :
(m ⊨[s] ¬ₜA) ↔ (m ⊭[s] A) := by
  simp only [L.not, holds, imp_false]

@[simp]
theorem holds_top (m : M) (s : m.S) :
(m ⊨[s] ⊤ₜ) := by
  simp only [L.top, L.not, holds, imp_self]

@[simp]
theorem holds_or (m : M) (s : m.S) (A B : L) :
(m ⊨[s] (A ∨ₜ B)) ↔ (m ⊨[s] A) ∨ (m ⊨[s] B) := by
  simp only [L.or, L.not, holds, imp_false]
  apply Iff.intro <;> grind only

@[simp]
theorem holds_and (m : M) (s : m.S) (A B : L) :
(m ⊨[s] (A ∧ₜ B)) ↔ (m ⊨[s] A) ∧ (m ⊨[s] B) := by
  simp only [L.and, L.not, holds, imp_false]
  apply Iff.intro <;> grind only

@[simp]
theorem holds_iff (m : M) (s : m.S) (A B : L) :
(m ⊨[s] (A ↔ₜ B)) ↔ ((m ⊨[s] A) ↔ (m ⊨[s] B)) := by
  simp only [L.iff, holds_and, holds]
  apply Iff.intro <;> grind only [cases Or]

@[simp]
theorem holds_dia (m : M) (s : m.S) (A : L) :
(m ⊨[s] (◇ₜA)) ↔ ∃ t : m.S, m.R s t ∧ (m ⊨[t] A) := by
  simp only [L.dia, L.not, holds, imp_false]
  apply Iff.intro <;> grind only

-- A formula is true in a model if it holds at all states in that model
@[simp]
def M.true (m : M) (A : L): Prop :=
  ∀ s : m.S, m ⊨[s] A
infix:50 " ⊨ₘ " => M.true

-- A formula is true in all models
@[simp]
def M.trueAll (A : L) : Prop :=
  ∀ (m : M), m ⊨ₘ A
prefix:max " ⊨ₘ " => M.trueAll

-- Validity in a frame
-- A formula is valid in a frame if it is true in all models based on that frame
@[simp]
def F.valid (f : F) (A : L): Prop :=
  ∀ v, (M.mk f v) ⊨ₘ A
infix:50 "⊨" => F.valid

-- A formula is valid in all frames
@[simp]
def F.validAll (A : L) : Prop :=
  ∀ (f : F), f ⊨ A
prefix:max "⊨" => F.validAll

@[simp]
theorem validAll_iff_trueAll (A : L) :
(⊨ A) ↔ (⊨ₘ A) := by
  apply Iff.intro
  · intro h m
    apply h m.toF
  · intro h f v
    apply h (M.mk f v)

-- Exercises 1.4

-- 1.4 (1)
example: ⊨ (□ₜ⊤ₜ : L) := by
  simp only [F.validAll, F.valid, M.true, holds, L.top, L.not, imp_self, implies_true]

-- K axiom
example (A B : L) : ⊨ (□ₜ(A →ₜ B) →ₜ (□ₜA →ₜ □ₜB)) := by
  simp only [F.validAll, F.valid, M.true, holds]
  grind only

example (A B : L) : ⊨ (◇ₜ(A →ₜ B) →ₜ (□ₜA →ₜ ◇ₜB)) := by
  simp
  grind only

example (A B : L) : ⊨ (□ₜ(A →ₜ B) →ₜ (◇ₜA →ₜ ◇ₜB)) := by
  simp only [F.validAll, F.valid, M.true, holds, L.dia, L.not, imp_false, Classical.not_forall,
    Classical.not_not, forall_exists_index]
  grind only

example (A B : L) : ⊨ (□ₜ(A ∧ₜ B) →ₜ (□ₜA ∧ₜ □ₜB)) := by
  simp
  grind only

example (A B : L) : ⊨ (◇ₜ(A ∨ₜ B) →ₜ (◇ₜA ∨ₜ ◇ₜB)) := by
  simp
  grind only

-- 1.4 (3)
-- Exhibit a frame in which □⊥ is valid
-- The frame with no worlds and no accessible worlds
example : ⟨Fin 0, λ _ _ => False⟩ ⊨ (□ₜ⊥ₜ : L) := by
  aesop
