
import LOTAC.Formula

-- A logic is a set of formulas containing all tautologies and
-- closed under detachment (MP)
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
notation " ⊬[" Λ "] " A => ¬ ⊢[Λ] A

-- We can define implication over a list of formulae
-- Using foldr to right associate the implications
notation:60 L " ⋯→ₜ " A => List.foldr (fun x₁ x₂ => x₁ →ₜ x₂) A L

-- Base Theorems ==============================================================

theorem Theorem.Ax1 : ⊢[Λ] B →ₜ (A →ₜ B) := by
  apply Λ.tauto; simp; grind

theorem Theorem.Ax2 : ⊢[Λ] A →ₜ (B →ₜ C) →ₜ ((A →ₜ B) →ₜ (A →ₜ C)) := by
  apply Λ.tauto; simp; grind

theorem Theorem.Ax3 : ⊢[Λ] ¬ₜ¬ₜA →ₜ A := by
  apply Λ.tauto; simp

theorem Theorem.mp : (⊢[Λ] A) → (⊢[Λ] A →ₜ B) → (⊢[Λ] B) := by
  intro H1 H2
  apply Λ.detach H1 H2

theorem Theorem.A_imp_A : ⊢[Λ] A →ₜ A := by
  apply Λ.tauto; simp

theorem Theorem.swap_antecedent: (⊢[Λ] A →ₜ B →ₜ C) → (⊢[Λ] B →ₜ A →ₜ C) := by
  intro H1
  have H2 : ⊢[Λ] (A →ₜ B →ₜ C) →ₜ B →ₜ A →ₜ C := by apply Λ.tauto; simp; grind
  apply Λ.detach H1 H2

theorem Theorem.weaken (H : ⊢[Λ] A) : ⊢[Λ] B →ₜ A := by
  have H1 : ⊢[Λ] A →ₜ (B →ₜ A) := by apply Λ.tauto; simp; grind
  exact Λ.detach H H1

theorem Theorem.if_intro : (⊢[Λ] B) → (⊢[Λ] A) → (⊢[Λ] B →ₜ A) := by
  intro _ H
  apply H.weaken

theorem Theorem.contrapose_imp : ⊢[Λ] (A →ₜ B) →ₜ (¬ₜB →ₜ ¬ₜA) := by
  apply Λ.tauto; simp; grind

theorem Theorem.contrapose_imp_rev : ⊢[Λ] (¬ₜB →ₜ ¬ₜA) →ₜ (A →ₜ B) := by
  apply Λ.tauto; simp; grind

theorem meta_contrapose_iff :
  (⊢[Λ] (A →ₜ B)) ↔ (⊢[Λ] (¬ₜB →ₜ ¬ₜA)) := by
  apply Iff.intro
  · case mp =>
    intro H1
    apply Theorem.mp H1 Theorem.contrapose_imp
  · case mpr =>
    intro H1
    apply Theorem.mp H1 Theorem.contrapose_imp_rev

-- Foldr Theorems =============================================================

theorem Theorem.weaken_list {Γ : List L} :
(⊢[Λ] A) → ⊢[Λ] (Γ ⋯→ₜ A) := by
  intro H
  induction Γ
  . case nil => simp_all only [List.foldr_nil]
  . case cons h t ih =>
    simp_all
    apply Theorem.weaken
    exact ih

theorem Theorem.weaken_middle
(H: ⊢[Λ] B →ₜ A) : ⊢[Λ] B →ₜ Γ ⋯→ₜ A := by
  induction Γ
  . case nil => simp_all only [List.foldr_nil]
  . case cons h t ih =>
    simp_all
    apply Theorem.swap_antecedent
    exact ih.weaken

theorem Theorem.cons {B : L} {Γ1 : List L} :
(⊢[Λ] (Γ1 ⋯→ₜ A)) → ⊢[Λ] ((B :: Γ1) ⋯→ₜ A) :=
  weaken

theorem Theorem.append_antes {Γ1 Γ2 : List L} :
(⊢[Λ] Γ1 ⋯→ₜ A) → ⊢[Λ] (Γ2 ++ Γ1) ⋯→ₜ A := by
  intro H
  induction H1: Γ1 <;> induction Γ2 <;> simp_all
  · case nil.cons h t ih => exact ih.weaken
  · case cons.cons h t ih => exact ih.weaken

theorem Theorem.position_irrelevant
(H : ⊢[Λ] B →ₜ A) (H2: B ∈ Γ) : ⊢[Λ] Γ ⋯→ₜ A := by
  induction Γ
  . case nil =>
    simp only [List.not_mem_nil] at H2
  . case cons h t ih =>
    simp_all
    cases H2
    . case inl H3 =>
      rw [<-H3]
      exact H.weaken_middle
    . case inr H3 =>
      exact (ih H3).weaken

theorem Theorem.weaken_arbitrary
(H1 : ⊢[Λ] Γ1 ⋯→ₜ A) : ∃ Γ2, (∀ B ∈ Γ1, B ∈ Γ2) ∧ ⊢[Λ] Γ2 ⋯→ₜ A := by
  grind

theorem Theorem.foldr_weaken
(H1 : ⊢[Λ] Γ1 ⋯→ₜ A) (H2 : Γ1 ⊆ Γ2) : ⊢[Λ] Γ2 ⋯→ₜ A := by
  let Γ3 : List L := Γ2.filter (fun x => !Γ1.contains x)
  have H3 : ∀x ∈ Γ2, x ∈ Γ1 ++ Γ3 := by
    intro x a
    simp_all only [List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, true_and, Γ3]
    rw [<-List.contains_iff_mem]
    have H4 := Classical.em (Γ1.contains x)
    simp_all only [Bool.not_eq_true, Bool.eq_true_or_eq_false_self]






















theorem Theorem.append_antes' {Γ1 Γ2 : List L} :
(⊢[Λ] Γ1 ⋯→ₜ A) → ⊢[Λ] (Γ1 ++ Γ2) ⋯→ₜ A := by
  intro H
  have H2 := @Theorem.append_antes _ _ Γ1 Γ2 H





theorem Theorem.assumption : ⊢[Λ] A :: Γ1 ⋯→ₜ A := by
  induction Γ1
  . case nil => exact .A_imp_A
  . case cons h t ih =>
    simp_all
    apply Theorem.swap_antecedent
    apply ih.weaken



-- theorem Theorem.foldr_swap {Γ1 Γ2 : List L} :
--   (⊢[Λ] (Γ1 ⋯→ₜ Γ2 ⋯→ₜ A)) → ⊢[Λ] (Γ2 ⋯→ₜ Γ1 ⋯→ₜ A) := by
--   sorry
--   sorry
--   intro H
--   induction Γ2 <;> induction Γ1 <;> simp_all
--   . case cons.cons h1 t1 h2 t2 ih1 ih2 =>
--     intro H
--     apply Theorem.if_intro

--     suffices ⊢[Λ] t1 ⋯→ₜ h2 →ₜ t2 ⋯→ₜ A by apply Λ.weaken  this



-- theorem theorem_contrapose_foldr {Γ : List L} :
--   (⊢[Λ] (Γ ⋯→ₜ A →ₜ B)) ↔ (⊢[Λ] (¬ₜB →ₜ Γ ⋯→ₜ ¬ₜA)) := by
--   induction Γ
--   . case nil =>
--     simp_all only [List.foldr]
--     apply meta_contrapose_iff
--   . case cons h t ih =>
--     simp_all only [List.foldr]
--     apply Iff.intro
--     · case mp =>
--       intro H1


-- Deducibility with Lists ====================================================

@[simp]
def DeducibleList (Λ : Logic) (Γ : List L) (A : L) :=
  ⊢[Λ] Γ ⋯→ₜ A

notation Γ " ⊢ₗ[" Λ "] " A => DeducibleList Λ Γ A

--1
theorem theorem_iff_empty_deduces_list : (⊢[Λ] A) ↔ [] ⊢ₗ[Λ] A := by
  aesop

theorem theorem_implies_any_deduces_list (H : ⊢[Λ] A) : Γ ⊢ₗ[Λ] A := by
  induction Γ
  . case nil => aesop
  . case cons h t ih => exact ih.weaken

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
      exact Theorem.assumption
    . case inr H2 =>
      exact (ih H2).weaken

-- 5
-- theorem deducible_subset_list (H1 : Γ ⊆ Δ) (H2 : Γ ⊢ₗ[Λ] A) : Δ ⊢ₗ[Λ] A := by
--   let L := Δ.filter (fun x => !Γ.contains x)
--   have Δ = Γ ++ L := by
--   sorry
  -- induction Γ
  -- . case nil =>
  --   simp_all
  --   have := @theorem_implies_any_deduces_list _ _ Δ H2
  --   exact this
  -- . case cons h t ih =>

    -- by_cases C1 : (⊢[Λ] h)
    -- · case pos =>
    --   apply ih
    --   simp_all
    --   have : ⊢[Λ] t.foldr (· →ₜ ·) A := Λ.mp C1 H2
    --   exact this
    -- · case neg =>
    --   apply ih
    --   simp_all
    --   --apply @Logic.mp Λ h _
    --   simp_all




    -- apply ih

-- 6
theorem detatchment_list (H1 : Γ ⊢ₗ[Λ] A) (H2 : Γ ⊢ₗ[Λ] A →ₜ B) : Γ ⊢ₗ[Λ] B := by
  sorry


@[simp]
def Deducible (Λ : Logic) (Γ : Set L) (A : L) :=
  ∃ (Bs : List L), (∀ B ∈ Bs, B ∈ Γ) ∧ Bs ⊢ₗ[Λ] A

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
--   . case nil => simp_all [Λ.weaken ]
--   . case cons h t ih => simp_all


-- theorem theorem_antes_append {Γ1 Γ2 : List L} :
-- (⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ1 ++ Γ2).foldr (· →ₜ ·) A) := by
--   intro H
--   simp_all
--   induction Γ1 <;> induction Γ2 <;> simp_all
--   · case nil.cons h t ih => exact Λ.weaken  ih
--   · case cons.cons h t ih1 ih2 =>

-- theorem theorem_fold' {Γ1 Γ2 : List L} :
-- (⊢[Λ] (Γ1.foldr (· →ₜ ·) A)) → ⊢[Λ] ((Γ1 ++ Γ2).foldr (· →ₜ ·) A) := by
--   intro H
  -- induction H1:Γ2 <;> induction H2:Γ1 <;>
  -- · case nil.nil => aesop
  -- · case nil.cons h t ih => simp_all
  -- · case cons.nil h t ih =>  simp_all; exact Λ.weaken  ih
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
  apply Theorem.A_imp_A

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
--     exact Λ.weaken  ih




-- theorem deduction : ((Γ ∪ {A}) ⊢[Λ] B) ↔ (Γ ⊢[Λ] A →ₜ B) := by
--   apply Iff.intro
--   · case mp =>
--     intro H1
--     sorry
--   · case mpr =>
--     intro H1
--     have H2 : (Γ ∪ {A}) ⊢[Λ] A →ₜ B := by apply deducible_subset (by grind) H1
