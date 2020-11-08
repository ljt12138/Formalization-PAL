-- Copyright (C) 2020 by @ljt12138

import tactic pal.basics

namespace pal_logic

def Ax1 {α agent : Type} (φ ψ : sentence α agent) := 
  φ ↣ ψ ↣ φ
def Ax2 {α agent : Type} (φ ψ γ : sentence α agent) := 
  (φ ↣ ψ ↣ γ) ↣ (φ ↣ ψ) ↣ φ ↣ γ
def Ax2' {α agent : Type} (φ : sentence α agent) :=
  φ ↣ (φ↣⊥) ↣ ⊥
def Ax3 {α agent : Type} (φ : sentence α agent) := 
  ((φ↣⊥)↣⊥) ↣ φ
def Ax3' {α agent : Type} (φ ψ : sentence α agent) :=
  (φ↣ψ) ↣ ((φ↣⊥)↣ψ) ↣ ψ
def Ax4 {α agent : Type} (φ ψ : sentence α agent) (i : agent) := 
  □(i : φ↣ψ) ↣ □(i : φ) ↣ □(i : ψ)
def AxR {α agent : Type} (φ : sentence α agent) (i : agent) :=
  □(i : φ) ↣ φ
def AxT {α agent : Type} (φ : sentence α agent) (i : agent) :=
  □(i : φ) ↣ □(i : □(i : φ))
def AxS {α agent : Type} (φ : sentence α agent) (i : agent) :=
  (□(i : φ)↣⊥) ↣ □(i : □(i : φ)↣⊥)

inductive proof (α agent : Type) : Type
| ax1 (φ ψ : sentence α agent)              : proof
| ax2 (φ ψ γ : sentence α agent)            : proof
| ax2' (φ : sentence α agent)               : proof
| ax3 (φ : sentence α agent)                : proof
| ax3' (φ ψ : sentence α agent)             : proof
| ax4 (φ ψ : sentence α agent) (i : agent)  : proof
| ref (φ : sentence α agent) (i : agent)    : proof
| trans (φ : sentence α agent) (i : agent)  : proof
| sym (φ : sentence α agent) (i : agent)    : proof
| mp                                        : proof → proof → proof
| truth                                     : proof → proof
| conj (Γ₁ Γ₂ : list (sentence α agent)) (φ : sentence α agent)   
                : proof → Γ₁ ⊆ Γ₂ → proof 
| conjl (φ ψ γ : sentence α agent)          : proof 
| conjr (φ ψ γ : sentence α agent)          : proof
| conjmp (φ ψ : sentence α agent)           : proof
| uncurry (φ ψ γ : sentence α agent)        : proof
| curry (φ ψ γ : sentence α agent)          : proof

@[simp] def conjunction {α agent : Type} :
  list (sentence α agent) → sentence α agent 
| []             := ⊥ ↣ ⊥
| [φ]            := φ
| (φ :: Γ)       := φ & conjunction Γ

inductive proof_of {α agent : Type} : 
  proof α agent → sentence α agent → Prop 
| ax1 (φ ψ : sentence α agent)              : proof_of (proof.ax1 φ ψ) (Ax1 φ ψ)
| ax2 (φ ψ γ : sentence α agent)            : proof_of (proof.ax2 φ ψ γ) (Ax2 φ ψ γ)
| ax2' (φ : sentence α agent)               : proof_of (proof.ax2' φ) (Ax2' φ)
| ax3 (φ : sentence α agent)                : proof_of (proof.ax3 φ) (Ax3 φ)
| ax3' (φ ψ: sentence α agent)              : proof_of (proof.ax3' φ ψ) (Ax3' φ ψ)
| ax4 (φ ψ : sentence α agent) (i : agent)  : proof_of (proof.ax4 φ ψ i) (Ax4 φ ψ i)
| ref (φ : sentence α agent) (i : agent)    : proof_of (proof.ref φ i) (AxR φ i)
| trans (φ : sentence α agent) (i : agent)  : proof_of (proof.trans φ i) (AxT φ i)
| sym (φ : sentence α agent) (i : agent)    : proof_of (proof.sym φ i) (AxS φ i)
| mp (φ ψ : _) (p q : proof α agent)        : proof_of p (φ↣ψ) → proof_of q φ 
                                              → proof_of (proof.mp p q) ψ
| truth (φ : _) (i : _) (p : proof α agent) : proof_of p φ 
                                              → proof_of (proof.truth p) □(i : φ)
| conj (Γ₁ Γ₂ : _) (φ : _) (h : Γ₁ ⊆ Γ₂) (p : proof α agent)
              : proof_of p (conjunction Γ₁ ↣ φ) → 
                proof_of (proof.conj Γ₁ Γ₂ φ p h) (conjunction Γ₂ ↣ φ)
| conjl (φ ψ γ : sentence α agent) (p : proof α agent)
              : proof_of p (φ ↣ γ) → proof_of (proof.conjl φ ψ γ) (φ & ψ ↣ γ)
| conjr (φ ψ γ : sentence α agent) (p : proof α agent)
              : proof_of p (ψ ↣ γ) → proof_of (proof.conjr φ ψ γ) (φ & ψ ↣ γ)
| conjmp (φ ψ : sentence α agent) : proof_of (proof.conjmp φ ψ) ((φ↣ψ)&φ↣ψ)
| uncurry (φ ψ γ : sentence α agent) (p : proof α agent)
              : proof_of p (φ↣ψ↣γ) → proof_of (proof.uncurry φ ψ γ) (φ&ψ↣γ)
| curry (φ ψ γ : sentence α agent) (p : proof α agent)
              : proof_of p (φ&ψ↣γ) → proof_of (proof.curry φ ψ γ) (φ↣ψ↣γ)

def provable {α agent : Type} (φ : sentence α agent) :=
  ∃ pf, proof_of pf φ 

prefix `⊢`:35 := provable

@[simp] def inconsistent {α agent : Type} (Γ : list (sentence α agent)) := 
  ⊢ (conjunction Γ) ↣ ⊥
@[simp] def consistent {α agent : _} (Γ : list (sentence α agent)) := 
  ¬ inconsistent Γ

meta def prover_core : tactic unit :=
do
  goal ← tactic.target,
  match goal with
  | `(proof_of %%pf %%φ)    := match pf with
                            | `(proof.ax1 _ _)     := tactic.applyc ``proof_of.ax1
                            | `(proof.ax2 _ _ _)   := tactic.applyc ``proof_of.ax2
                            | `(proof.ax2' _)      := tactic.applyc ``proof_of.ax2'
                            | `(proof.ax3 _)       := tactic.applyc ``proof_of.ax3
                            | `(proof.ax3' _ _)    := tactic.applyc ``proof_of.ax3'
                            | `(proof.ax4 _ _ _)   := tactic.applyc ``proof_of.ax4
                            | `(proof.ref _ _)     := tactic.applyc ``proof_of.ref
                            | `(proof.trans _ _)   := tactic.applyc ``proof_of.trans
                            | `(proof.sym _ _)     := tactic.applyc ``proof_of.sym
                            | `(proof.mp _ _)      := tactic.applyc ``proof_of.mp
                            | `(proof.truth _)     := tactic.applyc ``proof_of.truth
                            | `(proof.conj _ _ _ _ _)  := tactic.applyc ``proof_of.conj
                            | `(proof.conjl _ _ _) := tactic.applyc ``proof_of.conjl
                            | `(proof.conjr _ _ _) := tactic.applyc ``proof_of.conjr
                            | `(proof.conjmp _ _)  := tactic.applyc ``proof_of.conjmp
                            | `(proof.uncurry _ _ _) := tactic.applyc ``proof_of.uncurry
                            | `(proof.curry _ _ _) := tactic.applyc ``proof_of.curry
                            | _                    := tactic.assumption
                                                      <|>
                                                      tactic.tautology
                            end
  | _                      := tactic.fail "not a valid target"
  end

meta def prover : tactic unit :=
do
  tactic.repeat prover_core,
  tactic.done

end pal_logic

