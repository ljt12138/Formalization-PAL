-- Copyright (C) 2020 by @ljt12138

import propositional.basics propositional.thms data.list 
import propositional.used_formula

namespace prop_logic

lemma consistent_with_smaller_set {α : Type} (Γ Γ' : list (sentence α)) :
  Γ ⊆ Γ' → consistent Γ' → consistent Γ := 
begin
  intros h a contra,
  unfold consistent at a, apply a, 
  apply provable_with_stronger_assumption, 
  assumption, assumption, 
end

lemma consistent_with_append {α : Type} (Γ : list _) (φ : sentence α) : 
  consistent (φ :: Γ) → consistent Γ := 
begin
  intros h, 
  have ht : Γ ⊆ φ :: Γ := by simp, 
  apply consistent_with_smaller_set, assumption, assumption
end

lemma complete_extension {α : Type} {Γ : list (sentence α)} 
      (l : list (sentence α)) (a : consistent Γ) :
  ∃ Γ', Γ ⊆ Γ' ∧ (∀ φ, φ ∈ l → φ ∈ Γ' ∨ (~φ) ∈ Γ') ∧ consistent Γ' :=  
begin
  induction l with φ l' ih, 
  case nil { simp, existsi Γ, split, simp, assumption },
  case cons {
    cases ih with Γ₀ h, simp at *, 
    cases (classical.em (Γ₀ ⊢ φ)),
    case inl {
      existsi (list.cons φ Γ₀), split,
      { apply list.subset.trans, exact h.left, by simp },
      split, split,
      { simp }, 
      { simp, intros, have ht := h.right.left x H, tauto }, 
      {
        apply appending_provable, exact h.right.right,
        assumption
      }
    }, 
    case inr {
      existsi (list.cons (φ↣⊥) Γ₀), split, 
      { apply list.subset.trans, exact h.left, by simp }, 
      split, split, 
      { simp },
      { simp, intros, have ht := h.right.left x H, tauto },
      { apply appending_unprovable, assumption }
    }
  }
end

end prop_logic

