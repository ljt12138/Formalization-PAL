-- Copyright (C) 2020 by @ljt12138

import tactic pal.basics pal.proof 

namespace pal_logic

lemma mp_conseq {α agent : Type} {φ ψ : sentence α agent} : 
  ⊨ φ ↣ ψ → ⊨ φ → ⊨ ψ :=
begin
  intros a₁ a₂, simp at *, 
  intros, apply a₁, apply a₂
end

lemma conjunction_truth {α agent W : Type} (Γ : list (sentence α agent)) 
  (M : worlds α agent W) (s : W) : (M, s) ⊨ conjunction Γ ↔ ∀ φ, φ ∈ Γ → (M, s) ⊨ φ :=
begin
  split,
  {
    intros a, induction Γ with φ Γ ih, 
    simp, simp at *, 
    cases Γ, { simp at *, assumption },
    split, simp at *, 
    classical, by_contra, apply a, intros, apply a_1, exact a_2, 
    intros φ h, 
    apply ih, classical, by_contra, apply a, intros, simp, intro, exact a_1, 
    exact h
  },
  {
    intros a, induction Γ with φ Γ ih, 
    simp, simp at *, 
    cases Γ, { simp at *, assumption },
    intros a₁, 
    apply a₁, exact a.left, apply ih, exact a.right
  }
end

theorem soundness {α agent : Type} (φ : sentence α agent) :
  ⊢ φ → ⊨ φ :=
begin
  intros, cases a with pf a,
  induction a,
  case ax1 { 
    unfold Ax1, simp, intros, assumption
  },
  case ax2 {
    unfold Ax2, simp, intros, exact a a_2 (a_1 a_2)
  },
  case ax3 {
    unfold Ax3, simp, intros, classical, tauto
  },
  case ax4 {
    unfold Ax4, simp, intros, exact a _ a_2 (a_1 _ a_2)
  },
  case ref {
    unfold AxR, simp, intros, apply a s, 
    have ht := M.equiv a_i, 
    unfold equivalence at ht,
    exact ht.left s 
  },
  case trans {
    unfold AxT, simp, intros, apply a, 
    have ht := M.equiv a_i,
    unfold equivalence at ht, 
    apply ht.right.right, assumption, assumption
  },
  case sym {
    unfold AxS, simp, intros W M s a₁ t a₂ a₃,
    have a₄ := not_forall.mp a₁,
    cases a₄ with x h,
    apply h,intros h₁, apply a₃, 
    have ht := M.equiv a_i, unfold equivalence at ht,
    apply ht.right.right,
    { apply ht.right.left, assumption },
    { assumption }
  }, 
  case mp {
    apply mp_conseq, assumption, assumption
  },
  case truth {
    simp at *, intros, 
    apply a_ih
  },
  case conj {
    simp at *, intros W M s a₁, 
    have h₁ := (conjunction_truth a_Γ₂ M s).mp a₁,
    apply a_ih W M s, 
    apply (conjunction_truth _ _ _).mpr, 
    intros, apply h₁, exact a_h a
  },
  case ax2' { unfold Ax2', simp, intros, exact a_2 a_1 },
  case ax3' { unfold Ax3', simp, intros, classical, tauto },
  repeat { simp at *, intros, classical, tauto },
  case curry {
    simp at *, intros,  apply a_ih, intros contra,
    exact contra a a_1
  }
end 

end pal_logic

