
import LOTAC.Formula

-- A logic is a set of formulas containing all tautologies and closed under detachment (MP)
structure Logic where
  S : Set L
  tauto {A : L}: A.tautology → A ∈ S
  detach {A B : L} : A ∈ S → (A →ₜ B) ∈ S → B ∈ S

instance : HasSubset Logic where
  Subset Λ Λ' := Λ.S ⊆ Λ'.S

instance : Membership L Logic where
  mem Λ A := A ∈ Λ.S

-- The members of a logic are its theorems

def Theorem (Λ : Logic) (A : L) := A ∈ Λ.S

notation " ⊢[" Λ "] " A => Theorem Λ A

-- Important Theorems

theorem Logic.Ax1 : ⊢[Λ] B →ₜ (A →ₜ B) := by
  apply Λ.tauto; simp; grind

theorem Logic.Ax2 : ⊢[Λ] A →ₜ (B →ₜ C) →ₜ ((A →ₜ B) →ₜ (A →ₜ C)) := by
  apply Λ.tauto; simp; grind

theorem Logic.Ax3 : ⊢[Λ] ¬ₜ¬ₜA →ₜ A := by
  apply Λ.tauto; simp

theorem Logic.A_imp_A : ⊢[Λ] A →ₜ A := by
  apply Λ.tauto; simp

theorem theorem_swap_antecedent: (⊢[Λ] A →ₜ B →ₜ C) → (⊢[Λ] B →ₜ A →ₜ C) := by
  intro H1
  have H2 : ⊢[Λ] (A →ₜ B →ₜ C) →ₜ B →ₜ A →ₜ C := by apply Λ.tauto; simp; grind
  apply Λ.detach H1 H2

theorem theorem_B_implies_theorem_A_imp_B : (⊢[Λ] B) → (⊢[Λ] A →ₜ B) := by
  intro H1
  have H2 : ⊢[Λ] B →ₜ (A →ₜ B) := by apply Λ.tauto; simp; grind
  have H3 : ⊢[Λ] A →ₜ B := Λ.detach H1 H2
  exact H3

theorem theorem_cons {B : L} {Γ1 : List L} :
(⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((B :: Γ1).foldr (· →ₜ ·) A) := by
  intro H
  simp
  exact theorem_B_implies_theorem_A_imp_B H

theorem theorem_append_antes {Γ1 Γ2 : List L} :
(⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ2 ++ Γ1).foldr (· →ₜ ·) A) := by
  intro H
  induction H1: Γ1 <;> induction Γ2 <;> simp_all
  · case nil.cons h t ih => exact theorem_B_implies_theorem_A_imp_B ih
  · case cons.cons h t ih => exact theorem_B_implies_theorem_A_imp_B ih

theorem theorem_assumption : (⊢[Λ] ((A :: Γ1).foldr (· →ₜ ·) A)) := by
  induction Γ1
  . case nil => exact Logic.A_imp_A
  . case cons h t ih =>
    simp_all
    apply theorem_swap_antecedent
    apply theorem_B_implies_theorem_A_imp_B ih


@[simp]
def DeducibleList (Λ : Logic) (Γ : List L) (A : L) :=
  ⊢[Λ] (Γ.foldr (· →ₜ ·) A)

notation Γ " ⊢ₗ[" Λ "] " A => DeducibleList Λ Γ A

--1
theorem theorem_iff_empty_deduces_list : (⊢[Λ] A) ↔ [] ⊢ₗ[Λ] A := by
  aesop

theorem theorem_implies_any_deduces_list (H : ⊢[Λ] A) : Γ ⊢ₗ[Λ] A := by
  induction Γ
  . case nil => aesop
  . case cons h t ih => exact theorem_B_implies_theorem_A_imp_B ih

-- 3
theorem deducible_monotone_list (H1 : Λ ⊆ Λ') (H2 : Γ ⊢ₗ[Λ] A) : Γ ⊢ₗ[Λ'] A := by
  aesop

-- 4
theorem A_in_Gamma_implies_deducible_list (H : A ∈ Γ) : Γ ⊢ₗ[Λ] A := by
  induction Γ
  · case nil => aesop
  . case cons h t ih =>
    simp_all
    cases H
    . case inl H2 =>
      rw [H2]
      exact theorem_assumption
    . case inr H2 =>
      exact theorem_B_implies_theorem_A_imp_B (ih H2)

-- 5
theorem deducible_subset_list (H1 : Γ ⊆ Δ) (H2 : Γ ⊢ₗ[Λ] A) : Δ ⊢ₗ[Λ] A := by
  induction Γ
  . case nil =>
    simp_all
    have := @theorem_implies_any_deduces_list _ _ Δ H2
    exact this
  . case cons h t ih =>
    simp_all only [List.cons_subset]
    simp_all
    sorry
  -- simp_all
  -- induction Γ <;> induction Δ
  -- . case nil.nil => aesop
  -- . case nil.cons h t ih => simp_all; exact theorem_B_implies_theorem_A_imp_B ih
  -- . case cons.nil h t ih => aesop
  -- . case cons h1 t1 h2 t2 ih1 ih2 =>
  --   simp? at H1
  --   have ⟨H11, H12⟩ := H1
  --   clear H1
  --   cases H11
  --   have ih2' := ih2 H12
  --   apply ih2'
  --   -- . case inl C1 =>
  -- induction Δ
  -- . case nil => aesop
  -- . case cons h t ih =>
  --   simp_all [List.subset_cons]

    -- cases Γ
    -- . case nil => simp at ih; exact theorem_B_implies_theorem_A_imp_B ih
    -- . case cons h2 t2 =>











-- 6
theorem detatchment_list (H1 : Γ ⊢ₗ[Λ] A) (H2 : Γ ⊢ₗ[Λ] A →ₜ B) : Γ ⊢ₗ[Λ] B := by
  sorry


@[simp]
def Deducible (Λ : Logic) (Γ : Set L) (A : L) :=
  ∃ (Bs : List L), (∀ B ∈ Bs, B ∈ Γ) ∧ ⊢[Λ] (Bs.foldr (· →ₜ ·) A)

-- Yes, it should be foldr
-- inductive Lang where
-- | atom : Nat -> Lang
-- | imp : Lang -> Lang -> Lang
-- instance : MaterialImplication Lang := ⟨Lang.imp⟩
-- def A : Lang := Lang.atom 1
-- def B : Lang := Lang.atom 2
-- def C : Lang := Lang.atom 3
-- def D : Lang := Lang.atom 4

-- #eval [B, C, D].foldr (· →ₜ ·) A

@[simp]
def Deducible' (Λ : Logic) (Γ : Set L) (A : L) :=
  ∃ (n : Nat) (Bs : Fin n -> L), (∀ n, Bs n ∈ Γ) ∧ ⊢[Λ] (Fin.foldr n (Bs · →ₜ ·) A)

notation Γ " ⊢[" Λ "] " A => Deducible Λ Γ A

notation Γ " ⊬[" Λ "] " A => ¬Deducible Λ Γ A


@[simp]
def Consistent (Λ : Logic) (Γ : Set L) := Γ ⊬[Λ] ⊥ₜ

variable {Λ Λ' : Logic} {A B C: L} {Γ Δ : Set L}



-- theorem theorem_cons_back {Γ1: List L} :
-- (⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ1 ++ [B]).foldr (· →ₜ ·) A) := by
--   intro H
--   induction Γ1
--   . case nil => simp_all [theorem_B_implies_theorem_A_imp_B]
--   . case cons h t ih => simp_all


-- theorem theorem_antes_append {Γ1 Γ2 : List L} :
-- (⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ1 ++ Γ2).foldr (· →ₜ ·) A) := by
--   intro H
--   simp_all
--   induction Γ1 <;> induction Γ2 <;> simp_all
--   · case nil.cons h t ih => exact theorem_B_implies_theorem_A_imp_B ih
--   · case cons.cons h t ih1 ih2 =>

-- theorem theorem_fold' {Γ1 Γ2 : List L} :
-- (⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ1 ++ Γ2).foldr (· →ₜ ·) A) := by
--   intro H
  -- induction H1:Γ2 <;> induction H2:Γ1 <;>
  -- · case nil.nil => aesop
  -- · case nil.cons h t ih => simp_all
  -- · case cons.nil h t ih =>  simp_all; exact theorem_B_implies_theorem_A_imp_B ih
  -- · case cons.cons h1 t1 ih1 h2 t2 ih2 =>
  --   simp [H2] at ih1
  --   sorry

-- Exersizes 2.2

-- 1
theorem theorem_iff_empty_deduces : (⊢[Λ] A) ↔ ∅ ⊢[Λ] A := by
  apply Iff.intro
  · case mp =>
    intro H
    exists []
  · case mpr =>
    intro ⟨Γ, ⟨H1, H2⟩⟩
    have : Γ = [] := by
      cases Γ
      · case nil => rfl
      · case cons x xs =>
          have : x ∉ x :: xs := H1 x
          grind
    rw [this] at H2
    exact H2

-- 2

theorem theorem_implies_any_deduces (H : ⊢[Λ] A) : Γ ⊢[Λ] A := by
  exists []
  simp_all

-- 3
theorem deducible_monotone (H1 : Λ ⊆ Λ') (H2 : Γ ⊢[Λ] A) : Γ ⊢[Λ'] A := by
  aesop

-- 4
theorem A_in_Gamma_implies_deducible (H : A ∈ Γ) : Γ ⊢[Λ] A := by
  exists [A]
  simp_all
  apply Logic.A_imp_A

-- 5
theorem deducible_subset (H1 : Γ ⊆ Δ) (H2 : Γ ⊢[Λ] A) : Δ ⊢[Λ] A := by
  aesop?

-- 6
theorem detatchment (H1 : Γ ⊢[Λ] A) (H2 : Γ ⊢[Λ] A →ₜ B) : Γ ⊢[Λ] B := by
  have ⟨Γ1, ⟨H11, H12⟩⟩ := H1
  have ⟨Γ2, ⟨H21, H22⟩⟩ := H2
  sorry
--   have
--   have H12' : ⊢[Λ] List.foldr (fun x1 x2 ↦ x1 →ₜ x2) A (Γ1 ++ Γ2) := by
--     exact theorem_fold H12
--   clear H1 H2
--   exists Γ1 ++ Γ2
--   constructor
--   · case left =>
--     intro B H3
--     simp_all
--     aesop
--   induction H4 : Γ1 ++ Γ2
--   · case nil =>
--     simp_all
--     exact Λ.Mp H12 H22
--   · case cons h t ih  =>
--     rewrite [H4]
--     exact theorem_B_implies_theorem_A_imp_B ih




-- theorem deduction : ((Γ ∪ {A}) ⊢[Λ] B) ↔ (Γ ⊢[Λ] A →ₜ B) := by
--   apply Iff.intro
--   · case mp =>
--     intro H1
--     sorry
--   · case mpr =>
--     intro H1
--     have H2 : (Γ ∪ {A}) ⊢[Λ] A →ₜ B := by apply deducible_subset (by grind) H1
