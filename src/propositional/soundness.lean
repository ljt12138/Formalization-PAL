-- Copyright (C) 2020 by @ljt12138

import propositional.basics tactic.tauto

namespace prop_logic

lemma ax1_valid {α : Type} {φ ψ : sentence α} : tautology (Ax1 φ ψ) :=
begin
  unfold Ax1 tautology, simp, tauto
end

lemma ax1_conseq {α : Type} {φ ψ : sentence α} {Γ : _} : Γ ⊨ Ax1 φ ψ :=
begin
  unfold Ax1 logical_consequence contradiction_set, simp, 
  intros a, existsi _, split,
  { left, refl },
  { unfold evaluate, intro contra, apply contra, tauto }
end

lemma ax2_valid {α : Type} {φ ψ γ : sentence α} : tautology (Ax2 φ ψ γ) := 
begin
  unfold Ax2 tautology, simp, intros, exact a a_2 (a_1 a_2)
end

lemma ax2_conseq {α : Type} {φ ψ γ : sentence α} {Γ : _} : Γ ⊨ Ax2 φ ψ γ :=
begin
  unfold Ax2 logical_consequence contradiction_set, simp, 
  intros a, existsi _, split, 
  { left, refl },
  { unfold evaluate, intro contra, apply contra, intros, exact a_1 a_3 (a_2 a_3) }
end

lemma ax3_valid {α : Type} {φ : sentence α} : tautology (Ax3 φ) := 
begin
  unfold Ax3 tautology, simp, classical, tauto
end

lemma ax3_conseq {α : Type} {φ : sentence α} {Γ : _} : Γ ⊨ Ax3 φ :=
begin
  unfold Ax3 logical_consequence contradiction_set, simp,   
  intros a, existsi _, split,
  { left, refl },
  { unfold evaluate, intro contra, apply contra, classical, tauto }
end

lemma mp_valid {α : Type} {φ ψ : sentence α} : 
               tautology (φ ↣ ψ) → tautology φ → tautology ψ := 
begin
  unfold tautology, simp at *, tauto 
end

lemma mp_conseq {α : Type} {φ ψ : sentence α} {Γ : _} :
  Γ ⊨ φ ↣ ψ → Γ ⊨ φ → Γ ⊨ ψ :=
begin
  intros a a', 
  unfold logical_consequence contradiction_set at *, simp at *, 
  intros V, cases a' V, cases a V, 
  cases h, cases h_1, 
  cases h_left, 
  case or.inl {
    rewrite h_left at *,
    cases h_1_left,
    case or.inl {
      existsi _, split, {left, refl}, 
      rewrite h_1_left at *, 
      unfold evaluate at *, classical, tauto,   
    }, 
    case or.inr {
      existsi _, split, {right, assumption}, 
      assumption
    }
  },
  case or.inr {
    existsi _, split, {right, assumption}, 
    assumption
  }
end

theorem weak_soundness {α : Type} {φ : sentence α} : 
        ∅ ⊢ φ → tautology φ := 
begin
  intros a, cases a, 
  induction a_h, 
  { exact ax1_valid },
  { exact ax2_valid },
  { exact ax3_valid },
  { apply mp_valid, assumption, assumption },
  { cases a_h_a }
end

theorem strong_soundness {α : Type} {φ : sentence α} {Γ : _} : 
        Γ ⊢ φ → Γ ⊨ φ := 
begin
  intros a, cases a, 
  induction a_h,
  { exact ax1_conseq }, 
  { exact ax2_conseq },
  { exact ax3_conseq },
  { apply mp_conseq, assumption, assumption }, 
  { 
    unfold logical_consequence contradiction_set, intros V, 
    have ht := classical.em (evaluate V a_h_φ), cases ht, 
    { existsi a_h_φ↣⊥, split, {left, refl}, {simp, assumption} },
    { existsi a_h_φ, split, {right, assumption}, {assumption} }
  }
end

end prop_logic

