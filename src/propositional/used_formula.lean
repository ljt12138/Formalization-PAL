-- Copyright (C) 2020 by @ljt12138

import propositional.basics propositional.thms
import data.list

namespace prop_logic

@[simp] def used_formula {α : Type} : sentence α → list (sentence α)
| ⟦p⟧          := [ ⟦p⟧ ]
| ⊥            := [ ⊥ ]
| (φ ↣ ψ)      := (φ ↣ ψ) :: (used_formula φ ++ used_formula ψ)

@[simp] def used_formula_set {α : Type} : list (sentence α) → list (sentence α)
| []           := []
| (φ :: Γ)     := used_formula φ ++ used_formula_set Γ

notation `⦃` x `⦄` := used_formula x
notation `⦃` x `⦄` := used_formula_set x

lemma used_self {α : Type} (φ : sentence α) : φ ∈ ⦃ φ ⦄ :=
begin
  cases φ, 
  simp, simp, simp 
end

lemma used_chl {α : Type} (γ : sentence α) (φ ψ : sentence α) : 
  (φ ↣ ψ) ∈ ⦃ γ ⦄ → φ ∈ ⦃ γ ⦄ ∧ ψ ∈ ⦃ γ ⦄ := 
begin
  intros a, induction γ, 
  { simp, repeat {cases a} },
  { simp, repeat {cases a} }, 
  split, 
  { 
    simp at a, cases a, 
    { rewrite a.left, simp, right, left, exact used_self _ },
    cases a, 
    { simp, right, left, exact (γ_ih_a a).left },
    { simp, right, right, exact (γ_ih_a_1 a).left }
  },
  {
    simp at a, cases a, 
    { rewrite a.right, simp, right, right, exact used_self _ }, 
    cases a, 
    { simp, right, left, exact (γ_ih_a a).right },
    { simp, right, right, exact (γ_ih_a_1 a).right }
  }
end

lemma used_set_contains {α : Type} (Γ : list (sentence α)) (φ : _) :
  φ ∈ Γ → φ ∈ ⦃ Γ ⦄ :=
begin
  intros a, induction Γ,
  { simp at *, assumption }, 
  { 
    simp at *, cases a,
    { rewrite a, left, exact used_self _ },
    { right, exact Γ_ih a }
  }
end

lemma used_set_chl {α : Type} (Γ : list (sentence α)) (φ ψ : _) : 
  (φ ↣ ψ) ∈ ⦃ Γ ⦄ → φ ∈ ⦃ Γ ⦄ ∧ ψ ∈ ⦃ Γ ⦄ :=
begin
  intros a, induction Γ, 
  { simp at *, assumption }, 
  { 
    simp at *, cases a, 
    { 
      split, 
      { left, exact (used_chl _ _ _ a).left }, 
      { left, exact (used_chl _ _ _ a).right }
    },
    {
      cases Γ_ih a with ih ih', 
      split,
      repeat { tauto }
    }
  }
end

end prop_logic

