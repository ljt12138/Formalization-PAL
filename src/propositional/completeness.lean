-- Copyright (C) 2020 by @ljt12138

import propositional.used_formula 
import propositional.complete_extension

namespace prop_logic

def decidable_in {α : Type} (φ : sentence α) (Γ : list (sentence α)) := 
  φ ∈ Γ ∨ (~φ) ∈ Γ

lemma consistent_decidable_good {α : Type} (φ : sentence α) (Γ : list (sentence α)) :
  consistent Γ → decidable_in φ Γ → Γ ⊢ φ → φ ∈ Γ := 
begin
  intros c a a', 
  cases a, assumption, 
  simp at *,
  have ht : Γ ⊢ φ ↣ ⊥, { existsi proof.assum _, prover },
  exfalso, unfold consistent at c, 
  apply c, cases a', cases ht, 
  existsi proof.mp _ _, prover   
end

lemma complete_extension_on_used {α : Type} {Γ : list (sentence α)} (a : consistent Γ) :
  ∃ Γ', Γ ⊆ Γ' ∧ (∀ φ, φ ∈ ⦃Γ⦄ → decidable_in φ Γ') ∧ consistent Γ' := 
begin
  unfold decidable_in, apply complete_extension, assumption
end

lemma consistent_to_satisfiable {α : Type} {Γ : list (sentence α)} 
  (a : consistent Γ) : satisfiable_set Γ :=
begin
  cases (complete_extension_on_used a) with Γ' h, 
  existsi (λ (p : α), ⟦p⟧ ∈ Γ'),  
  intros φ a, 
  have gres : ∀ φ, φ ∈ ⦃Γ⦄ → (evaluate (λ (p : α), ⟦p⟧ ∈ Γ') φ ↔ φ ∈ Γ'), { 
    intros φ, induction φ, 
    case atom_prop { simp }, 
    case perp { 
      simp, intros a' contra,
      have ht := h.right.right, unfold consistent at ht, apply ht, 
      existsi proof.assum _, prover
    }, 
    case imply {
      simp at *, intros a₁, 
      cases used_set_chl _ _ _ a₁ with a₁' a₁'',
      have ih₁ := φ_ih_a a₁',
      have ih₂ := φ_ih_a_1 a₁'',
      have ih' := h.right.left _ a₁,
      have ih₃ := h.right.left _ a₁',
      have ih₄ := h.right.left _ a₁'',
      split,
      { 
        intros a₂, cases ih',
        { assumption },
        { 
          cases ih₃,  
          { 
            have res := inside_provable (ih₂.mp (a₂ (ih₁.mpr ih₃))), 
            apply consistent_decidable_good, tauto, tauto,
            apply useless_condition, assumption
          }, 
          {
            simp at *, 
            exfalso, apply h.right.right, 
            have pf_ih' := inside_provable ih', 
            have pf_ih₃ := inside_provable ih₃, 
            exact false_condition pf_ih' pf_ih₃
          }
        }
      }, 
      {
        intros a₂ a₃, apply ih₂.mpr, 
        have a₃' := inside_provable (ih₁.mp a₃),
        have a₂' := inside_provable a₂,
        apply consistent_decidable_good, tauto, tauto, 
        cases a₂', cases a₃', 
        existsi proof.mp _ _, prover 
      }
    }
  },
  have ins : φ ∈ ⦃Γ⦄ := by exact used_set_contains _ _ a, 
  apply (gres φ ins).mpr, 
  exact h.left a, 
end 

theorem completeness {α : Type} {Γ : _} {φ : sentence α} :
  Γ ⊨ φ → Γ ⊢ φ := 
begin
  intros a, 
  unfold logical_consequence at *,  
  have h := contra_of_not_satis a, 
  apply provable_contra.mpr, simp, 
  have ht : ¬ (consistent ((φ↣⊥)::Γ)), 
  { intros contra, apply h, apply consistent_to_satisfiable, assumption },
  unfold consistent at ht, classical, tauto
end

end prop_logic

