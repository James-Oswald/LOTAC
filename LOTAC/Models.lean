
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import LOTAC.Formula

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

-- Auxiliary holds theorems for defined connectives

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

-- Truth in a model

-- A formula is true in a model if it holds at all states in that model
@[simp]
def M.true (m : M) (A : L): Prop :=
  ∀ s : m.S, m ⊨[s] A

infix:50 " ⊨ₘ " => M.true
notation m " ⊭ₘ " A => ¬(m ⊨ₘ A)

-- A formula is true in all models
@[simp]
def M.true_all (A : L) : Prop :=
  ∀ (m : M), m ⊨ₘ A

prefix:max " ⊨ₘ " => M.true_all
notation " ⊭ₘ " A => ¬⊨ₘ A

-- A schema is true in a model if all its instances are true in that model
@[simp]
def M.schema_true (m : M) (A :L) :=
  ∀ i ∈ Schema A, m ⊨ₘ i
infix:50 " ⊨ₘₛ " => M.schema_true
notation m " ⊭ₘₛ " A => ¬(m ⊨ₘₛ A)

-- A schema is true in all models if all its instances are true in all models
@[simp]
def M.schema_true_all (A : L) :=
  ∀ m : M, m ⊨ₘₛ A
prefix:max " ⊨ₘₛ " => M.schema_true_all
notation " ⊭ₘₛ " A => ¬⊨ₘₛ A

-- Schema truth implies truth of the formula, but not vice versa
theorem schema_true_all_imp_true_all :
(⊨ₘₛ A) → (⊨ₘ A) := by
  intro h m s
  apply h m
  exact A_in_Schema_A

theorem not_true_all_imp_schema_not_true_all :
(⊭ₘ A) → (⊭ₘₛ A) := by
  contrapose!
  exact schema_true_all_imp_true_all

-- Validity in a frame

-- A formula is valid in a frame iff it is true in all models based on that frame
@[simp]
def F.valid (f : F) (A : L): Prop :=
  ∀ v, ⟨f, v⟩ ⊨ₘ A

infix:50 "⊨" => F.valid
notation f "⊭" A => ¬(f ⊨ A)

-- A formula is valid in all frames iff it is true in all models based on those frames
@[simp]
def F.valid_all (A : L) : Prop :=
  ∀ (f : F), f ⊨ A
prefix:max "⊨" => F.valid_all
notation "⊭" A => ¬⊨ A

-- Validity of a schema in a frame
@[simp]
def F.schema_valid (f : F) (A : L) :=
  ∀ i ∈ Schema A, f ⊨ i
infix:50 "⊨ₛ" => F.schema_valid
notation f "⊭ₛ" A => ¬(f ⊨ₛ A)

-- A schema is valid in all frames iff all its instances are valid in all frames
@[simp]
def F.schema_valid_all (A : L) :=
  ∀ f : F, f ⊨ₛ A
prefix:max "⊨ₛ" => F.schema_valid_all
notation "⊭ₛ" A => ¬⊨ₛ A

@[simp]
theorem valid_all_iff_true_all :
(⊨ A) ↔ (⊨ₘ A) := by
  apply Iff.intro
  · intro h m
    apply h m.toF
  · intro h f v
    apply h (M.mk f v)

@[simp]
theorem not_valid_all_iff_not_true_all :
(⊭ A) ↔ (⊭ₘ A) := by
  apply not_iff_not.mpr
  apply valid_all_iff_true_all

@[simp]
theorem schema_valid_all_iff_true_all :
(⊨ₛ A) ↔ (⊨ₘₛ A) := by
  simp_all only [F.schema_valid_all, F.schema_valid, F.valid, M.true, M.schema_true_all, M.schema_true]
  apply Iff.intro
  · intro a m i a_1 s
    simp_all only
  · intro a f i a_1 v s
    simp_all only

@[simp]
theorem schema_not_valid_iff_not_schema_true_all :
(⊭ₛ A) ↔ (⊭ₘₛ A) := by
  apply not_iff_not.mpr
  apply schema_valid_all_iff_true_all

-- Countermodel existence theorems

-- If a formula is not true in all models, then there is a countermodel
theorem not_true_iff_exists_countermodel:
(⊭ₘ A) ↔ ∃ m : M, (m ⊭ₘ A) := by
  simp_all only [M.true_all, M.true, not_forall]

theorem not_valid_iff_exists_countermodel:
(⊭ A) ↔ ∃ m : M, (m ⊭ₘ A) := by
  calc
    (⊭ A) ↔ (⊭ₘ A) := not_valid_all_iff_not_true_all
    _ ↔ ∃ m : M, (m ⊭ₘ A) := not_true_iff_exists_countermodel

theorem not_valid_iff_exists_counterframe:
(⊭ A) ↔ ∃ f : F, (f ⊭ A) := by
  simp_all only [F.valid_all, F.valid, M.true, not_forall]

theorem schema_not_true_iff_schema_exists_countermodel:
(⊭ₘₛ A) ↔ ∃ m : M, ∃ i ∈ Schema A, (m ⊭ₘ i) := by
  simp_all

theorem schema_not_valid_iff_schema_exists_counterframe:
(⊭ₛ A) ↔ ∃ f : F, ∃ i ∈ Schema A, (f ⊭ i) := by
  simp_all

theorem schema_not_valid_iff_schema_exists_countermodel:
(⊭ₛ A) ↔ ∃ m : M, ∃ i ∈ Schema A, (m ⊭ₘ i) := by
  calc
    (⊭ₛ A) ↔ (⊭ₘₛ A) := schema_not_valid_iff_not_schema_true_all
    _ ↔ ∃ m : M, ∃ i ∈ Schema A, (m ⊭ₘ i) := schema_not_true_iff_schema_exists_countermodel

theorem exists_countermodel_imp_schema_not_valid :
 (∃ m : M, (m ⊭ₘ A)) → (⊭ₛ A) := by
    intro H
    apply schema_not_valid_iff_not_schema_true_all.mpr
    apply not_true_all_imp_schema_not_true_all
    apply not_true_iff_exists_countermodel.mpr
    exact H

-- Exercises 1.4

-- 1.4 (1)
example: ⊨ (□ₜ⊤ₜ : L) := by
  simp only [F.valid_all, F.valid, M.true, holds, L.top, L.not, imp_self, implies_true]

-- K axiom
example : ⊨ (□ₜ(A →ₜ B) →ₜ (□ₜA →ₜ □ₜB)) := by
  simp only [F.valid_all, F.valid, M.true, holds]
  grind only

example : ⊨ (◇ₜ(A →ₜ B) →ₜ (□ₜA →ₜ ◇ₜB)) := by
  simp
  grind only

example : ⊨ (□ₜ(A →ₜ B) →ₜ (◇ₜA →ₜ ◇ₜB)) := by
  simp only [F.valid_all, F.valid, M.true, holds, L.dia, L.not, imp_false, Classical.not_forall,
    Classical.not_not, forall_exists_index]
  grind only

example : ⊨ (□ₜ(A ∧ₜ B) →ₜ (□ₜA ∧ₜ □ₜB)) := by
  simp_all only [F.valid_all, F.valid, M.true, holds, L.and, L.not, imp_false, Classical.not_imp, not_not, implies_true,
    not_true_eq_false]

example : ⊨ (◇ₜ(A ∨ₜ B) →ₜ (◇ₜA ∨ₜ ◇ₜB)) := by
  simp
  grind only


-- 1.4 (2) Show the the following do not have the property of validity in all frames
-- NB: some instances of these s
example : ⊭ₛ □ₜA1 →ₜ A1 := by
  apply exists_countermodel_imp_schema_not_valid
  -- Any non-reflexive frame will do
  exists {
    S := Fin 1,
    R := λ w1 w2 => False,
    V := λ a w => False
  }
  simp

example : ⊭ₛ □ₜA1 →ₜ □ₜ□ₜA1 := by
  apply exists_countermodel_imp_schema_not_valid
  -- 0 -> 1 -> 2
  -- A    A   ¬A
  exists {
    S := Fin 3,
    R := λ w1 w2 => w1 = 0 ∧ w2 = 1 ∨ w1 = 1 ∧ w2 = 2,
    V := λ a w => w ≠ 2
  }
  simp_all

example : ⊭ₛ □ₜ(A1 →ₜ A2) →ₜ (□ₜA1 →ₜ ◇ₜA2) := by
  apply exists_countermodel_imp_schema_not_valid
  exists {
    S := Fin 1,
    R := λ w1 w2 => False,
    V := λ a w => False
  }
  simp

example : ⊭ₛ ◇ₜ⊥ₜ := by
  apply exists_countermodel_imp_schema_not_valid
  exists {
    S := Fin 1,
    R := λ w1 w2 => False,
    V := λ a w => False
  }
  simp

example : ⊭ₛ ◇ₜA1 →ₜ □ₜA1 := by
  apply exists_countermodel_imp_schema_not_valid
  --  1 <- 0 -> 2
  --  A   ¬A   ¬A
  exists {
    S := Fin 3,
    R := λ w1 w2 => w1 = 0 ∧ (w2 = 1 ∨ w2 = 2),
    V := λ a w => w = 1
  }
  simp_all

example : ⊭ₛ □ₜ(□ₜA1 →ₜ A2) ∨ₜ □ₜ(□ₜA2 →ₜ A1) := by
  apply exists_countermodel_imp_schema_not_valid
  --  1 <- 0 -> 2
  --  A   ¬A   ¬A
  --  ¬B  ¬B    B
  exists {
    S := Fin 3,
    R := λ w1 w2 => w1 = 0 ∧ (w2 = 1 ∨ w2 = 2),
    V := λ a w => (a = 1 ∧ w = 1) ∨ (a = 2 ∧ w = 2)
  }
  simp_all

-- Godel Lob axiom
example : ⊭ₛ □ₜ(□ₜA1 →ₜ A1) →ₜ □ₜA1 := by
  apply exists_countermodel_imp_schema_not_valid
  -- 1 (self loop)
  -- ¬A
  exists {
    S := Fin 1,
    R := λ w1 w2 => w1 = 0 ∧ w2 = 0,
    V := λ a w => False
  }
  simp

-- 1.4 (3)
-- Show that ◇ₜ⊤ₜ and the schema □ₜA1 →ₜ ◇ₜA1 have the same class of models
-- That is, show that a model satisfies one iff it satisfies the other
example (m : M) :
(m ⊨ₘ (◇ₜ⊤ₜ : L)) ↔ (m ⊨ₘₛ (□ₜA1 →ₜ ◇ₜA1)) := by
  apply Iff.intro
  · intro H s sH
    sorry
  · intro
    sorry

-- 1.4 (4)
-- Exhibit a frame in which □⊥ is valid
-- The frame with no worlds and no accessible worlds
example : ⟨Fin 0, λ _ _ => False⟩ ⊨ (□ₜ⊥ₜ : L) := by
  aesop

-- 1.4 (5)
-- Show that in any model M
-- (i) if A is a tautology, then M ⊨ₘ A
-- (ii) if  M ⊨ₘ A and M ⊨ₘ A →ₜ B, then M ⊨ₘ B
-- (iii) if M ⊨ₘ A then M ⊨ₘ □ₜA

set_option pp.proofs true

theorem tautology_implies_model_true :
A.tautology → (m ⊨ₘ A) := by
  induction A
  · case atom a =>
    intro H
    simp [L.tautology] at H
    have H2 := H (λ _ => False)
    simp at H2
  . case bot => simp [L.tautology]
  . case imp a1 a2 ih1 ih2 =>
    intro H
    simp at H
    sorry
  . case box a1 ih =>
    intro H
    simp_all
    have H2 := H (λ _ => False)
    simp at H2

theorem model_true_implies_model_imp_true :
(m ⊨ₘ A) → (m ⊨ₘ (A →ₜ B)) → (m ⊨ₘ B) := by
  intro H H1 s
  apply H1 s
  exact H s

theorem model_true_imp_model_box_true :
(m ⊨ₘ A) → (m ⊨ₘ □ₜA) := by
  intro H s t sRt
  exact H t

-- 1.4 (5)
-- The above three theorems can be done for any frame F rather than a model M

theorem tautology_implies_frame_valid :
A.tautology → (f ⊨ A) := by
  sorry

theorem frame_valid_implies_frame_imp_valid :
(f ⊨ A) → (f ⊨ (A →ₜ B)) → (f ⊨ B) := by
  intro a a_1
  simp_all only [F.valid, M.true, holds, forall_const, implies_true]

theorem frame_valid_imp_frame_box_valid :
(f ⊨ A) → (f ⊨ □ₜA) := by
  intro a
  simp_all only [F.valid, M.true, holds, implies_true]
