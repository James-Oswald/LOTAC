
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

variable {Φ : Type} [BEq Φ] [DecidableEq Φ]

set_option linter.unusedSectionVars false

inductive L where
| atom : Φ → L
| bot : L
| imp : L → L → L
| box : L → L
deriving DecidableEq

notation "⊥ₜ" => L.bot
infixr:30 " →ₜ " => L.imp
prefix:max " □ₜ" => L.box

@[simp]
def L.not (A : @L Φ) : @L Φ := A →ₜ ⊥ₜ
prefix:max " ¬ₜ" => L.not

@[simp]
def L.top : @L Φ := ¬ₜ⊥ₜ
notation "⊤ₜ" => L.top

@[simp]
def L.or (A B : @L Φ) : @L Φ := ¬ₜA →ₜ B
infixl:35 "∨ₜ" => L.or

@[simp]
def L.and (A B : @L Φ) : @L Φ := ¬ₜ(A →ₜ ¬ₜB)
infixl:40 "∧ₜ" => L.and

@[simp]
def L.iff (A B : @L Φ) : @L Φ := (A →ₜ B) ∧ₜ (B →ₜ A)
infix:20 "↔ₜ" => L.iff

@[simp]
def L.dia (A : @L Φ) : @L Φ := ¬ₜ□ₜ¬ₜA
prefix:max " ◇ₜ" => L.dia

-- Subformulae of a formula
@[simp]
def S : @L Φ -> Finset (@L Φ)
| .atom p => {.atom p}
| ⊥ₜ => {⊥ₜ}
| A→ₜB => {A→ₜB} ∪ S A ∪ S B
| □ₜA => {□ₜA} ∪ S A

-- Single substitution, replaces an atom p in A with B
@[simp]
def subst (A B : @L Φ) (p : Φ) : @L Φ :=
  match A with
  | .atom q => if p = q then B else .atom q
  | ⊥ₜ => ⊥ₜ
  | A1 →ₜ A2 => (subst A1 B p) →ₜ (subst A2 B p)
  | □ₜ A1 => □ₜ(subst A1 B p)

-- Multiple substitution
@[simp]
def msubst (A : @L Φ) : List (Φ × @L Φ) -> @L Φ
| [] => A
| (p, B) :: t => msubst (subst A B p) t

-- A' is a substitution instance of A
-- iff there exists a list of substitutions that when applied to A yield A'
@[simp]
def subst_inst (A A' : @L Φ) : Prop :=
  ∃ l : List (Φ × @L Φ), msubst A l = A'

-- A schema is a set of all substitution instances of a formula A
def Schema (A : @L Φ) : Set (@L Φ) :=
  { A' | subst_inst A A' }

-- Valuations and Tautologies
@[simp]
def L.isBox: @L Φ -> Bool
| □ₜ _ => True
| _ => False

@[simp]
def L.containsBox: @L Φ -> Bool
| .atom _ => False
| ⊥ₜ => False
| A →ₜ B => A.containsBox ∨ B.containsBox
| □ₜ _ => True

def L.propositional (A : @L Φ) : Bool :=
  ¬A.containsBox

@[simp]
def L.isAtomic : @L Φ -> Bool
| .atom _ => True
| _ => False

@[simp]
def L.quasiAtomic (A : @L Φ) : Bool :=
  A.isAtomic ∨ A.isBox

-- The type of quasi-atomic formula
@[simp]
abbrev Lq : Type := {A : @L Φ // A.quasiAtomic}

-- The type of quasi-atomic subformulae of A
def Sq (A : @L Φ) : Type := {B : @L Φ // B.quasiAtomic ∧ B ∈ S A}

-- Sq A is finite
instance (A : @L Φ) : Fintype (Sq A) := by
  apply Fintype.ofFinset ((S A).filter (·.quasiAtomic))
  intro x
  simp only [Finset.mem_filter, Set.instMembership, Set.Mem]
  grind

-- -- Subvaluation on quasi-atomic formulae
-- def Sv {A : @L Φ} (v : Sq A -> Bool) (B : @L Φ) : Sq B -> Bool :=
--   if h : B ∈ S A then
--   else
--     λ _ => False

-- Extension of a valuation on quasi-atomic formulae to all formulae
def V (f : @L Φ) (v : Sq f -> Bool) : Bool :=
match f with
| .atom p => v ⟨.atom p, by simp⟩
| ⊥ₜ => False
| A →ₜ B => (V A (Sv v )) → (V B (Sv v B))
| □ₜ A => v ⟨□ₜ A, by simp⟩

-- A formula is a tautology iff V v A holds for all quasi-atomic valuations v
def L.tautology (A : @L Φ) : Prop :=
  ∀ (v : @Lq Φ -> Bool), V v A
