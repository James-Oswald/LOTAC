
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Data.Finset.Max

inductive L where
| atom : Nat → L
| bot : L
| imp : L → L → L
| box : L → L
deriving DecidableEq, BEq, Inhabited

-- instance: LawfulBEq L where
--   eq_of_beq := by
--     intros a b H
--     induction a <;>
--     induction b <;>
--     simp only [BEq.beq] at H <;>
--     try contradiction
--     · case atom.atom a1 a2 =>
--       rw [instBEqL.beq] at H
--       simp
--       rw [<-Nat.beq_eq_true_eq]
--       exact H
--     · case bot.bot => rfl
--     · case imp.imp a1 a2 b1 b2 => --ih1 ih2 ih3 ih4 =>
--       rw [instBEqL.beq] at H
--       simp_all
--       sorry
--     . case box.box a1 b1 ih1 ih2 =>
--       rw [instBEqL.beq] at *
--       simp_all


notation "⊥ₜ" => L.bot
infixr:30 " →ₜ " => L.imp
prefix:max " □ₜ" => L.box

@[simp]
def L.not (A : L) : L := A →ₜ ⊥ₜ
prefix:max " ¬ₜ" => L.not

@[simp]
def L.top : L := ¬ₜ⊥ₜ
notation "⊤ₜ" => L.top

@[simp]
def L.or (A B : L) : L := ¬ₜA →ₜ B
infixl:35 "∨ₜ" => L.or

@[simp]
def L.and (A B : L) : L := ¬ₜ(A →ₜ ¬ₜB)
infixl:40 "∧ₜ" => L.and

@[simp]
def L.iff (A B : L) : L := (A →ₜ B) ∧ₜ (B →ₜ A)
infix:20 "↔ₜ" => L.iff

@[simp]
def L.dia (A : L) : L := ¬ₜ□ₜ¬ₜA
prefix:max " ◇ₜ" => L.dia

@[simp]
theorem a_neq_box_a : A ≠ □ₜA := by
  induction A <;> simp_all


-- Subformulae of a formula
@[simp]
def S : L -> Finset (L)
| .atom p => {.atom p}
| ⊥ₜ => {⊥ₜ}
| A→ₜB => {A→ₜB} ∪ S A ∪ S B
| □ₜA => {□ₜA} ∪ S A

-- Named atoms for schemas
@[simp] abbrev A1 : L := L.atom 1
@[simp] abbrev A2 : L := L.atom 2
@[simp] abbrev A3 : L := L.atom 3

-- All formulae are subformulae of themselves
theorem A_mem_S_A {A : L} : A ∈ S A := by
  induction A <;> aesop

-- Subformula membership is transitive
theorem mem_S_trans {A B C : L} : A ∈ S B ∧ B ∈ S C → A ∈ S C := by
  intro ⟨H1, H2⟩
  induction B <;> induction C <;> simp_all only [S] <;> grind

-- If A -> B is a subformula of C, then so are A and B
theorem mem_imp_mem {A B C: L} : (A →ₜ B) ∈ S C → A ∈ S C ∧ B ∈ S C := by
  induction C <;> simp_all only [S] <;> try grind [A_mem_S_A]

-- Single substitution, replaces an atom p in A with B
@[simp]
def subst (A B : L) (p : Nat) : L :=
  match A with
  | .atom q => if p = q then B else .atom q
  | ⊥ₜ => ⊥ₜ
  | A1 →ₜ A2 => (subst A1 B p) →ₜ (subst A2 B p)
  | □ₜ A1 => □ₜ(subst A1 B p)

-- Single substitution, replaces an C in A with B
-- @[simp]
-- def subst_f (A B C: L) : L :=
--   if A = C then
--     B
--   else
--     match A with
--     | .atom q => .atom q
--     | ⊥ₜ => ⊥ₜ
--     | A1 →ₜ A2 => (subst_f A1 B C) →ₜ (subst_f A2 B C)
--     | □ₜ A1 => □ₜ(subst_f A1 B C)

-- Multiple substitution
@[simp]
def msubst (A : L) : List (Nat × L) -> L
| [] => A
| (p, B) :: t => msubst (subst A B p) t

-- @[simp]
-- def msubst_f (A : L) : List (L × L) -> L
-- | [] => A
-- | (f, t) :: ts => msubst_f (subst_f A t f) ts

-- A' is a substitution instance of A
-- iff there exists a list of substitutions that when applied to A yield A'
@[simp]
def subst_inst (A A' : L) : Prop :=
  ∃ l : List (Nat × L), msubst A l = A'

-- @[simp]
-- def subst_inst (A A' : L) : Prop :=
--   ∃ l : List (L × L), msubst_f A l = A'

-- A schema is a set of all substitution instances of a formula A
@[simp]
def Schema (A : L) : Set (L) :=
  { A' | subst_inst A A' }

theorem A_in_Schema_A : A ∈ Schema A := by
  use []
  simp

-- Valuations and Tautologies

-- L is a boxed formula if it starts with a box
@[simp]
def L.isBox: L -> Bool
| □ₜ _ => True
| _ => False

-- L contains a box if any of its subformulae are boxed
@[simp]
def L.containsBox: L -> Bool
| .atom _ => False
| ⊥ₜ => False
| A →ₜ B => A.containsBox ∨ B.containsBox
| □ₜ _ => True

-- A contains a box iff a subformula of A is a box
theorem containsBox_iff_mem_S_isBox (A : L) : A.containsBox ↔ ∃ B ∈ S A, B.isBox := by
  induction A
  . case atom => simp
  . case bot => simp
  . case imp f1 f2 ih1 ih2 =>
    simp [-L.isBox]
    apply Iff.intro
    . case mp => grind
    . case mpr => simp_all; grind
  . case box => simp

-- A formula is propositional if it does not contain any boxes
def L.propositional (A : L) : Bool :=
  ¬A.containsBox

-- A formula is atomic if it is an atom
@[simp]
def L.isAtomic : L -> Bool
| .atom _ => True
| _ => False

@[simp]
def L.quasiAtomic (A : L) : Bool :=
  A.isAtomic ∨ A.isBox

-- The type of quasi-atomic formula
@[simp]
abbrev Lq : Type := {A : L // A.quasiAtomic}

-- The type of quasi-atomic subformulae of A
def Sq (A : L) : Type := {B : L // B.quasiAtomic ∧ B ∈ S A}

instance (A : L) : DecidableEq (Sq A) := by
  apply Subtype.instDecidableEq

-- Sq A is finite
instance (A : L) : Fintype (Sq A) := by
  apply Fintype.ofFinset ((S A).filter (·.quasiAtomic))
  intro x
  simp only [Finset.mem_filter, Set.instMembership, Set.Mem]
  grind

-- The type of valuations over Sq A is finite
instance (A : L) : Fintype (Sq A -> Bool) := by
  apply Pi.instFintype

-- Subvaluation of the formula f1 at subformula f2
@[simp]
def V_aux (f1 f2: L) (v : Sq f1 -> Bool) (H : f2 ∈ S f1): Bool :=
match H2: f2 with
| .atom p => v ⟨.atom p, by simpa⟩
| ⊥ₜ => False
| A →ₜ B => (V_aux f1 A v (mem_imp_mem H).left) → (V_aux f1 B v (mem_imp_mem H).right)
| □ₜ A => v ⟨□ₜ A, by simpa⟩

-- Valuation of a formula f1 with a function over its quasi-atomic subformulae
@[simp]
def V (f1 : L) (v : Sq f1 -> Bool) : Bool :=
  V_aux f1 f1 v (A_mem_S_A)

-- A formula is a tautology iff it holds for all quasi-atomic valuations
-- This is decidable thanks to Fintype (Sq A -> Bool), Fintype (Sq A)
@[simp]
def L.tautology (A : L) : Bool :=
  ∀ (v : Sq A -> Bool), V A v


-- def fresh_atom (A : L) : Φ :=
--   let used := S A |>.filter (·.isAtomic)
--   let used_n : Finset Nat := used.map (Encodable Φ).encode
--   let max : Nat := used_n.max'
--   Encodable.decode

-- -- Any tautology is a substitution instance of a propositional tautology
-- example (A: L) (TA : A.tautology):
-- ∃ (B : L), B.tautology ∧ B.propositional ∧ subst_inst B A := by


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
