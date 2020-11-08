-- Copyright (C) 2020 by @ljt12138

import tactic pal.basics pal.proof 

namespace pal_logic

lemma useless_condition {α agent : Type} (φ ψ : sentence α agent) :
  ⊢ ψ → ⊢ φ↣ψ :=
begin
  intros a,
  have ht : ⊢ ψ ↣ φ ↣ ψ, { existsi proof.ax1 _ _, prover },
  cases a, cases ht,
  existsi proof.mp _ _, prover
end

lemma id_provable {α agent : Type} (φ : sentence α agent) :
  ⊢ φ ↣ φ :=
begin
  existsi (proof.mp (proof.mp (proof.ax2 _ _ _) 
                              (proof.ax1 _ _)) 
                    (proof.ax1 φ φ)),
  prover
end

lemma hs_rule {α agent : Type} (φ ψ γ : sentence α agent) : 
  ⊢ φ ↣ ψ → ⊢ ψ ↣ γ → ⊢ φ ↣ γ :=
begin
  intros a₁ a₂,
  have h₁ : ⊢ φ ↣ ψ ↣ γ, { apply useless_condition, assumption },
  cases h₁, cases a₁,
  existsi proof.mp (proof.mp (proof.ax2 _ _ _) _) _, prover
end

lemma explosion {α agent : Type} (φ : sentence α agent) :
  ⊢ (⊥ : sentence α agent) ↣ φ :=
begin
  have h₁ : ⊢ (⊥ ↣ (φ ↣ ⊥) ↣ ⊥ : sentence α agent), 
  { existsi proof.ax1 _ _, prover },
  have h₂ : ⊢ ((φ ↣ ⊥) ↣ ⊥) ↣ φ, 
  { existsi proof.ax3 _, prover },
  apply hs_rule, repeat {assumption} 
end


lemma double_Γ_equiv {α agent : Type} (Γ : list (sentence α agent)) :
  consistent Γ → consistent (Γ++Γ) :=  
begin
  intros a₁, simp at *, intros a₂,
  apply a₁, clear a₁, 
  cases a₂, 
  existsi proof.conj _ _ _ _ _,
  apply proof_of.conj, exact a₂_h, simp
end

lemma mp_via_ax2 {α agent : Type} (φ ψ γ : sentence α agent) :
  ⊢ φ ↣ ψ ↣ γ → ⊢ φ ↣ ψ → ⊢ φ ↣ γ :=
begin
  intros a₁ a₂, cases a₁, cases a₂,
  existsi proof.mp (proof.mp (proof.ax2 _ _ _) _) _, prover
end

lemma uncurry {α agent : Type} (φ ψ γ : sentence α agent) :
  ⊢ φ ↣ ψ ↣ γ → ⊢ φ & ψ ↣ γ :=
begin
  intros a, cases a,
  existsi proof.uncurry _ _ _, prover
end

lemma curry {α agent : Type} (φ ψ γ : sentence α agent) :
  ⊢ φ & ψ ↣ γ → ⊢ φ ↣ ψ ↣ γ :=
begin
  intros a, cases a,
  existsi proof.curry _ _ _, prover
end

lemma dni {α agent : Type} (φ : sentence α agent) :
  ⊢ φ ↣ (φ↣⊥) ↣ ⊥ :=
begin
  have h₁ : ⊢ φ & (φ ↣ ⊥) ↣ φ,
  { apply uncurry, existsi proof.ax1 _ _, prover },
  have h₂ : ⊢ φ & (φ ↣ ⊥) ↣ (φ ↣ ⊥),
  { apply uncurry, apply useless_condition, apply id_provable },
  apply curry, apply mp_via_ax2, repeat {assumption}
end

lemma drop_mem {α : Type} (φ : α) (Γ : list α) : 
  ∃ Γ', Γ' ⊆ Γ ∧ φ ∉ Γ' ∧ Γ ⊆ φ :: Γ' :=
begin
  classical, 
  induction Γ with ψ Γ ih,
  { existsi list.nil, simp },
  {
    cases ih with Γ' ih₁,
    cases classical.em (φ = ψ), 
    {
      existsi Γ', split,
      { apply list.subset_cons_of_subset, exact ih₁.left }, split,
      { exact ih₁.right.left },
      { simp, split, { left, rewrite h }, { exact ih₁.right.right }}
    },
    {
      existsi (list.cons ψ Γ'), split,
      { simp, apply list.subset_cons_of_subset, exact ih₁.left }, split,
      { 
        intros contra, simp at contra, cases contra, 
        exact h contra, exact ih₁.right.left contra 
      },
      {
        simp, intros γ ht, 
        cases ih₁.right.right ht, 
        { rewrite h_1, simp },
        { simp, right, right, exact h_1 }
      }
    }
  }
end

lemma add_assumption {α agent : Type} {φ ψ : sentence α agent} {Γ : list _} :
  ⊢ φ & conjunction Γ ↣ ψ ↔ ⊢ conjunction (φ :: Γ) ↣ ψ :=
begin
  split,
  {
    intros h, cases Γ with ψ Γ',
    {
      have ht₁ := curry _ _ _ h, simp at ht₁, simp, 
      have ht₂ : ⊢ φ ↣ ((⊥ : sentence α agent) ↣ ⊥),
      { apply useless_condition, apply id_provable },
      cases ht₁, cases ht₂, 
      existsi (proof.mp (proof.mp (proof.ax2 _ _ _) _) _),
      prover
    },
    { unfold conjunction, exact h }
  },
  {
    intros h, cases Γ with ψ Γ',
    {
      simp at h, cases h,
      existsi proof.conjl _ _ _, prover
    },
    { unfold conjunction at h, exact h }
  }
end

lemma drop_assumption {α agent : Type} {φ ψ : sentence α agent} {Γ : list _} : 
  ⊢ φ & conjunction Γ ↣ ψ → ∃ Γ', Γ' ⊆ Γ ∧ φ ∉ Γ' ∧ ⊢ φ & conjunction Γ' ↣ ψ :=
begin
  intros h,
  cases drop_mem φ Γ with Γ' h₁, 
  existsi Γ', split,
  { exact h₁.left }, split,
  { exact h₁.right.left },
  {
    apply add_assumption.mpr, 
    have ht₁ := add_assumption.mp h, 
    have ht₂ : (list.cons φ Γ) ⊆ φ :: Γ', { simp, exact h₁.right.right }, 
    cases ht₁, existsi proof.conj _ _ _ _ _, 
    apply proof_of.conj, assumption, assumption 
  }
end 

lemma and_swap {α agent : Type} {φ ψ γ : sentence α agent} :
  ⊢ φ & ψ ↣ γ → ⊢ ψ & φ ↣ γ :=
begin
  have h₁ : ∀ φ ψ : sentence α agent, φ & ψ = conjunction [φ, ψ] := by simp, 
  rewrite h₁, rewrite h₁, 
  intros h₂,
  have h₃ : [φ, ψ] ⊆ [ψ, φ] := by simp, 
  cases h₂,
  existsi proof.conj _ _ _ _ _,
  apply proof_of.conj, assumption, assumption
end

lemma contra_imp_conseq {α agent : Type} {φ : sentence α agent} {Γ : list (sentence α agent)} :
  φ ∈ Γ → ⊢ conjunction Γ ↣ ⊥ → ∃ Γ', Γ' ⊆ Γ ∧ φ ∉ Γ' ∧ ⊢ conjunction Γ' ↣ (φ ↣ ⊥) :=
begin
  intros h₁ h₂,
  have h₃ : ⊢ (φ & conjunction Γ) ↣ ⊥, 
  { 
    apply add_assumption.mpr, cases h₂, 
    existsi proof.conj _ _ _ _ _, apply proof_of.conj, exact h₂_h, simp 
  },
  cases drop_assumption h₃ with Γ' h₄, 
  existsi Γ', split,
  { exact h₄.left }, split,
  { exact h₄.right.left },
  { apply curry, apply and_swap, exact h₄.right.right }
end

lemma conj_subset {α agent : Type} {φ : sentence α agent} {Γ₁ Γ₂ : list (sentence α agent)} :
  ⊢ conjunction Γ₁ ↣ φ → Γ₁ ⊆ Γ₂ → ⊢ conjunction Γ₂ ↣ φ :=
begin
  intros h₁ h₂,
  cases h₁, 
  existsi proof.conj _ _ _ _ _,
  apply proof_of.conj, exact h₁_h, exact h₂
end

end pal_logic
