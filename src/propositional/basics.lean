-- Copyright (C) 2020 by @ljt12138

namespace prop_logic 

/- Sentence and corresponding notations -/

inductive sentence (α : Type) : Type 
| atom_prop : α → sentence
| perp : sentence
| imply : sentence → sentence → sentence

notation `⟦` p `⟧` := sentence.atom_prop p
notation `⊥` := sentence.perp
infixr `↣`:55 := sentence.imply
prefix `~` := λ φ, φ ↣ ⊥
infixl `||` := λ φ ψ, (~φ) ↣ ψ
infixr `&&` := λ φ ψ, ~(φ ↣ (~ψ))

/- Model, evaluation and tautology -/

def model {α : Type} : Type := α → Prop 

@[simp]
def evaluate {α : Type} (V : model) : sentence α → Prop
| ⟦p⟧      := V p
| ⊥        := false
| (φ ↣ ψ)  := evaluate φ → evaluate ψ

def tautology {α : Type} (φ : sentence α) := ∀ V, evaluate V φ
def contradiction {α : Type} (φ : sentence α) := ∀ V, ¬(evaluate V φ)
def satisfiable {α : Type} (φ : sentence α) := ∃ V, evaluate V φ

def contradiction_set {α : Type} (Γ : list (sentence α)) := 
  ∀ V, ∃ φ, φ ∈ Γ ∧ ¬(evaluate V φ)
def satisfiable_set {α : Type} (Γ : list (sentence α)) := 
  ∃ V, ∀ φ, φ ∈ Γ → evaluate V φ 
def logical_consequence {α : Type} (Γ : _) (φ : sentence α) := 
  contradiction_set ((~φ) :: Γ)

infix `⊨`:30 := logical_consequence
 
/- Axioms -/

def Ax1 {α : Type} (φ ψ : sentence α) := φ ↣ ψ ↣ φ
def Ax2 {α : Type} (φ ψ γ : sentence α) := (φ ↣ ψ ↣ γ) ↣ (φ ↣ ψ) ↣ φ ↣ γ
def Ax3 {α : Type} (φ : sentence α) := (~~φ) ↣ φ

/- Proof -/

inductive proof (α : Type) : Type 
| ax1 (φ ψ : sentence α) : proof
| ax2 (φ ψ γ : sentence α) : proof
| ax3 (φ : sentence α) : proof
| assum (φ : sentence α) : proof
| mp : proof → proof → proof

inductive proof_of {α : Type} (Γ : list (sentence α)) : 
                   proof α → sentence α → Prop
| ax1 (φ ψ : _)          : proof_of (proof.ax1 φ ψ)   (Ax1 φ ψ)
| ax2 (φ ψ γ : _)        : proof_of (proof.ax2 φ ψ γ) (Ax2 φ ψ γ)
| ax3 (φ : _)            : proof_of (proof.ax3 φ)     (Ax3 φ)
| mp (φ ψ : _) (p q : _) : proof_of p (φ↣ψ) → proof_of q φ → proof_of (proof.mp p q) ψ
| assum (φ : _)          : φ ∈ Γ → proof_of (proof.assum φ) φ

def provable {α : Type} (Γ : list (sentence α)) (φ : sentence α) := 
  ∃ pf, proof_of Γ pf φ

infix `⊢`:30 := provable 

def consistent {α : Type} (Γ : list (sentence α)) := 
  ¬ (provable Γ ⊥)

end prop_logic

