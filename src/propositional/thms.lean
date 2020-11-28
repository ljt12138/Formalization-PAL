-- Copyright (C) 2020 by @ljt12138

import propositional.basics tactic

namespace prop_logic 

meta def prover_core : tactic unit := 
do
  goal ← tactic.target, 
  match goal with 
  | `(proof_of _ %%pf %%φ) := match pf with
                            | `(proof.ax1 _ _)   := tactic.applyc ``proof_of.ax1
                            | `(proof.ax2 _ _ _) := tactic.applyc ``proof_of.ax2
                            | `(proof.ax3 _)     := tactic.applyc ``proof_of.ax3
                            | `(proof.mp _ _)    := tactic.applyc ``proof_of.mp
                            | `(proof.assum _)   := do tactic.applyc ``proof_of.assum, 
                                                       tactic.assumption
                            | _                  := tactic.assumption 
                                                    <|> 
                                                    tactic.tautology
                            end 
  | _                    := tactic.fail "not a valid target"
  end

meta def prover : tactic unit := 
do
  tactic.repeat prover_core,
  tactic.done

lemma id_provable {α : Type} {φ : sentence α} {Γ : _} : Γ ⊢ (φ ↣ φ) := 
begin
  unfold provable, 
  existsi (proof.mp (proof.mp (proof.ax2 φ (φ↣φ) φ) 
                              (proof.ax1 φ (φ↣φ))) (proof.ax1 φ φ)), 
  prover
end

lemma useless_condition {α : Type} {φ ψ : sentence α} {Γ : _} :
  Γ ⊢ φ → Γ ⊢ (ψ ↣ φ) :=
begin
  intro a, 
  have pcut : provable Γ (φ ↣ ψ ↣ φ), {
    unfold provable, existsi proof.ax1 _ _, prover
  }, 
  cases a, cases pcut, 
  existsi (proof.mp pcut_w a_w),
  prover
end

theorem deduction (α : Type) (φ ψ : sentence α) (Γ : _) : 
  (φ::Γ) ⊢ ψ → Γ ⊢ (φ ↣ ψ) := 
begin
  intros a, unfold provable at a, cases a, 
  induction a_h, 
  repeat { 
    apply useless_condition,
    {existsi proof.ax1 _ _, prover} 
    <|> { existsi proof.ax2 _ _ _, prover } 
    <|> { existsi proof.ax3 _, prover }
  }, 
  case mp {
    cases a_h_ih_a, cases a_h_ih_a_1, 
    have ps : Γ ⊢ (Ax2 φ a_h_φ a_h_ψ), {
      unfold provable, existsi proof.ax2 _ _ _, prover
    }, cases ps, unfold Ax2 at ps_h, 
    existsi proof.mp (proof.mp _ _) _,
    prover
  },
  case assum {
    induction a_h_a, 
    case inl { rewrite ← a_h_a, apply id_provable }, 
    case inr {
      apply useless_condition, 
      existsi proof.assum a_h_φ, 
      prover, 
    }
  }
end

lemma provable_with_stronger_assumption {α : Type} {φ : sentence α} {Γ Γ' : _} :
  Γ ⊆ Γ' → Γ ⊢ φ → Γ' ⊢ φ := 
begin
  intros a a', cases a', 
  induction a'_h, 
  case ax1 { existsi proof.ax1 _ _, prover }, 
  case ax2 { existsi proof.ax2 _ _ _, prover },
  case ax3 { existsi proof.ax3 _, prover }, 
  case mp { cases a'_h_ih_a, cases a'_h_ih_a_1, existsi proof.mp _ _, prover },
  case assum { 
    have ht := a a'_h_a, 
    existsi proof.assum _, prover
  }
end

lemma provable_with_append {α : Type} {φ : sentence α} {Γ : _} (ψ : sentence α) :
  Γ ⊢ φ → ψ::Γ ⊢ φ :=
begin
  have ht := list.subset_cons ψ Γ, 
  intros a, apply provable_with_stronger_assumption, 
  assumption, assumption
end

def provably_equivalent {α : Type} (Γ Γ' : list (sentence α)) : Prop := 
  ∀ φ, (Γ ⊢ φ ↔ Γ' ⊢ φ)

infix ≡ := provably_equivalent

lemma provable_append {α : Type} {Γ : _} {φ : sentence α} :
  Γ ⊢ φ → Γ ≡ φ::Γ :=
begin
  intros a φ', split,
  {
    intros a', cases a', induction a'_h, 
    case ax1 { existsi proof.ax1 _ _, prover }, 
    case ax2 { existsi proof.ax2 _ _ _, prover }, 
    case ax3 { existsi proof.ax3 _, prover }, 
    case mp {
      cases a'_h_ih_a, cases a'_h_ih_a_1, 
      existsi proof.mp _ _, prover
    }, 
    case assum {
      have ht' := list.mem_cons_of_mem φ a'_h_a, 
      existsi proof.assum _, prover, 
    }
  }, 
  {
    intros a', cases a', induction a'_h, 
    case ax1 { existsi proof.ax1 _ _, prover }, 
    case ax2 { existsi proof.ax2 _ _ _, prover }, 
    case ax3 { existsi proof.ax3 _, prover }, 
    case mp {
      cases a'_h_ih_a, cases a'_h_ih_a_1, 
      existsi proof.mp _ _, prover
    }, 
    case assum {
      cases a'_h_a, 
      case or.inl { rewrite a'_h_a, assumption }, 
      case or.inr { existsi proof.assum _, prover }
    }
  }
end

lemma provable_contra {α : Type} {Γ : _} {φ : sentence α} : 
  Γ ⊢ φ ↔ (~φ)::Γ ⊢ ⊥ := 
begin
  split, 
  {
    intro a, simp, 
    have ht' := provable_with_append (φ↣⊥) a,
    have htt := list.mem_cons_self (φ↣⊥) Γ, 
    have ht2 : (φ↣⊥)::Γ ⊢ φ↣⊥, {existsi proof.assum _,  prover},
    cases ht', cases ht2, 
    existsi proof.mp _ _, prover, 
  }, 
  {
    intro a, simp at *, 
    have ht : Γ ⊢ ~~φ, simp, apply deduction, assumption, 
    have ht' : Γ ⊢ (~~φ)↣φ, {existsi proof.ax3 _, prover},
    simp at *, cases ht, cases ht', 
    existsi proof.mp _ _, prover
  }
end

lemma contra_of_not_satis {α : Type} {Γ : list (sentence α)} :
  contradiction_set Γ → ¬ satisfiable_set Γ :=
begin
  unfold contradiction_set satisfiable_set, 
  intros, apply not_exists_of_forall_not, intros V, 
  apply not_forall_of_exists_not, cases (a V), existsi w, tauto
end

lemma not_satis_of_contra {α : Type} {Γ : list (sentence α)} : 
  ¬ satisfiable_set Γ → contradiction_set Γ := 
begin
  unfold contradiction_set satisfiable_set,
  intros, have a' := forall_not_of_not_exists a V, 
  simp at a', cases a' with φ h, 
  existsi φ, assumption
end

lemma inside_provable {α : Type} {Γ : _} {φ : sentence α} : 
  φ ∈ Γ → Γ ⊢ φ :=
begin
  intros, existsi proof.assum _, prover
end

theorem appending_unprovable {α : Type} {Γ : _} {φ : sentence α} :
  ¬(Γ ⊢ φ) → consistent ((~φ)::Γ) :=
begin
  intros a contra, simp at *,
  have ht := provable_contra.mpr contra,
  exact a ht 
end

theorem appending_provable {α : Type} {Γ : _} {φ : sentence α} :
  consistent Γ → Γ ⊢ φ → consistent (φ::Γ) := 
begin
  intros a a', unfold consistent at *, 
  intro contra,
  exact a ((provable_append a' ⊥).mpr contra)
end

theorem explosion {α : Type} {Γ : list (sentence α)} {φ : sentence α} :
  Γ ⊢ ⊥ → Γ ⊢ φ := 
begin
  intros a, 
  apply provable_contra.mpr, simp, 
  exact provable_with_append _ a
end

lemma false_condition {α : Type} {Γ : _} {φ ψ : sentence α} :
  Γ ⊢ (φ ↣ ψ) ↣ ⊥ → Γ ⊢ φ ↣ ⊥ → Γ ⊢ ⊥ :=
begin
  intros a a',
  have ht : Γ ⊢ φ ↣ ψ, {
    apply deduction,
    have ht₁ := provable_with_append φ a',
    have ht₂ : φ ∈ (list.cons φ Γ) := by simp,
    have ht₃ : φ :: Γ ⊢ φ, { existsi proof.assum _, prover },
    have ht₄ : φ :: Γ ⊢ ⊥, {
      cases ht₁, cases ht₃, existsi proof.mp _ _, prover
    },
    apply explosion, assumption
  }, 
  cases a, cases ht, existsi proof.mp _ _, prover
end
 
end prop_logic

