-- Copyright (C) 2020 by @ljt12138

import tactic pal.basics pal.proof pal.henkin_model pal.lemmas

namespace pal_logic

/- explain_set Γ₁ Γ := `Γ₁ is a Γ-explain set of Γ`
 - Γ₁ is a Γ-explain set, if it is obtained by adding φ or ¬φ into it, for all φ ∈ Γ
 -/
@[simp] def explain_set {α agent : Type} (Γ₁ Γ : list (sentence α agent)) :=
  ∀ (φ : sentence α agent), φ ∈ Γ₁ → (φ ∈ Γ) ∨ (∃ ψ, φ = ψ ↣ ⊥ ∧ ψ ∈ Γ)

/- complete_set Γ₁ Γ := `Γ₁ is a Γ-complete set `
 - Γ₁ is a Γ-complete set if for every φ∈Γ, either φ∈Γ₁ or ¬φ∈Γ₁
 -/
@[simp] def complete_set {α agent : Type} (Γ₁ Γ : list (sentence α agent)) :=  
  ∀ (φ : sentence α agent), φ ∈ Γ → φ ∈ Γ₁ ∨ (φ ↣ ⊥) ∈ Γ₁

lemma single_extension {α agent : Type} (Γ : list _) (φ : sentence α agent) :
  consistent Γ → inconsistent (φ::Γ) → consistent ((φ↣⊥)::Γ) :=
begin
  simp, intros a₀ a₁ a₂,
  apply a₀, cases Γ with ψ Γ,
  { -- Γ = ∅
    simp at *, exfalso, apply a₀, apply useless_condition,
    cases a₁, cases a₂, existsi proof.mp _ _, 
    apply proof_of.mp, exact a₂_h, repeat {assumption}, 
  },
  have a₁' : ⊢ φ ↣ conjunction (ψ::Γ) ↣ ⊥,
  { apply curry, simp at *, assumption },
  have a₂' : ⊢ (φ ↣ ⊥) ↣ conjunction (ψ::Γ) ↣ ⊥,
  { apply curry, simp at *, assumption },
  cases a₁' with pf₁' h₁', cases a₂' with pf₂' h₂',
  existsi proof.mp _ _,
  apply proof_of.mp, apply proof_of.mp, 
  apply proof_of.ax3' φ, 
  assumption, assumption
end

lemma consistent_cons {α agent : Type} (Γ : list _) (φ : sentence α agent) :
  consistent (φ::Γ) → consistent Γ :=
begin
  cases Γ with ψ Γ, 
  { -- Γ = ∅
    simp, intros a contra,
    apply a, apply useless_condition,   
    have h := id_provable (⊥ : sentence α agent),
    cases contra, cases h,
    existsi proof.mp _ _, prover
  },
  intros a₁, simp at *, intros a₂, apply a₁,
  have ht := useless_condition φ _ a₂, cases ht with pf h,
  existsi proof.mp _ _, apply proof_of.mp,
  apply proof_of.ax2', exact h
end 

lemma extension {α agent : Type} (Γ Γ₁ l : list (sentence α agent)) :
  explain_set Γ₁ Γ → consistent Γ₁ → consistent (l ++ Γ) → 
    ∃ (Γ₂ : list _), Γ₁ ⊆ Γ₂ ∧ consistent Γ₂ ∧ explain_set Γ₂ (l ++ Γ)
          ∧ complete_set Γ₂ l :=
begin
  intros a₁ a₂, 
  induction l with φ l₁ ih,
  {
    simp at *, intros a, existsi Γ₁, split, 
    simp, split, exact a₂, exact a₁ 
  },
  {
    intros a₃, 
    cases ih (consistent_cons _ _ a₃) with Γ₂ h₁,
    cases (classical.em (inconsistent (φ::Γ₂))) with h₂,
    {
      existsi (list.cons (φ↣⊥) Γ₂), split,
      apply list.subset_cons_of_subset, exact h₁.left, split,
      apply single_extension, exact h₁.right.left, exact h₂, split,
      unfold explain_set, intros φ₁ a₄, cases a₄, 
      { right, existsi φ, split, exact a₄, simp },
      { 
        cases h₁.right.right.left φ₁ a₄, left, apply list.mem_cons_of_mem, exact h,
        cases h with ψ h, right, existsi ψ, split, exact h.left, 
        apply list.mem_cons_of_mem, exact h.right 
      },
      unfold complete_set, intros φ₁ h₃, 
      cases h₃, 
      { right, rewrite h₃, simp },
      {
        cases h₁.right.right.right φ₁ h₃,
        { left, apply list.mem_cons_of_mem, exact h },
        { right, apply list.mem_cons_of_mem, exact h }
      }
    },
    {
      existsi (list.cons φ Γ₂), split,
      apply list.subset_cons_of_subset, exact h₁.left, split,
      exact h, split,
      unfold explain_set, intros φ₁ a₄, cases a₄,
      { left, rewrite a₄, apply list.mem_cons_self },
      { 
        cases h₁.right.right.left φ₁ a₄, left, apply list.mem_cons_of_mem, exact h_1, 
        cases h_1 with ψ h_1, right, existsi ψ, split, exact h_1.left, 
        apply list.mem_cons_of_mem, exact h_1.right
      },
      unfold complete_set, intros φ₁ h₃, 
      cases h₃, 
      { left, rewrite h₃, apply list.mem_cons_self },
      { 
        cases h₁.right.right.right φ₁ h₃,
        { left, apply list.mem_cons_of_mem, exact h_1 },
        { right, apply list.mem_cons_of_mem, exact h_1 }
      }
    }
  }
end

theorem complete_extension {α agent : Type} (Γ Γ₁ : list (sentence α agent)) : 
  explain_set Γ₁ Γ → consistent Γ₁ → consistent Γ → ∃ Γ₂ : list (sentence α agent), 
    Γ₁ ⊆ Γ₂ ∧ consistent Γ₂ ∧ explain_set Γ₂ Γ ∧ complete_set Γ₂ Γ :=
begin
  intros a₁ a₂ a₃,
  have ht := extension Γ Γ₁ Γ a₁ a₂ (double_Γ_equiv _ a₃),
  cases ht with Γ₂ h, 
  existsi Γ₂, split, tauto, split, tauto, split, 
  simp, intros φ h₁, 
  cases h.right.right.left φ h₁,
  { left, simp at h_1, assumption },
  { right, cases h_1, existsi h_1_w, simp at h_1_h, exact h_1_h },
  exact h.right.right.right
end

end pal_logic
