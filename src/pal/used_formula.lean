-- Copyright (C) 2020 by @ljt12138

import pal.basics pal.proof
import data.list

namespace pal_logic

@[simp] def used_formula {α agent : Type} : sentence α agent → list (sentence α agent)
| ⟦p⟧          := [ ⟦p⟧ ]
| ⊥            := [ ⊥ ]
| (φ ↣ ψ)      := (φ ↣ ψ) :: (used_formula φ ++ used_formula ψ)
| □(i : φ)     := □(i : φ) :: used_formula φ
| [!φ]ψ        := ([!φ]ψ) :: (used_formula φ ++ used_formula ψ)

notation `⦃` x `⦄` := used_formula x

lemma used_self {α agent : Type} (φ : sentence agent α) : φ ∈ ⦃ φ ⦄ :=
begin
  cases φ, 
  repeat { simp } 
end

lemma used_imply {α agent : Type} (γ : sentence α agent) (φ ψ : sentence α agent) : 
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
  },
  {
    simp at a, simp, split,
    { right, exact (γ_ih a).left },
    { right, exact (γ_ih a).right }
  },
  {
    simp at a, cases a, 
    { 
      simp, split, right, left, exact (γ_ih_a a).left, 
      right, left, exact (γ_ih_a a).right 
    },
    { 
      simp, split, right, right, exact (γ_ih_a_1 a).left, 
      right, right, exact (γ_ih_a_1 a).right
    }
  }
end

lemma used_box {α agent : Type} (γ : sentence α agent) (φ : _) (i : agent) :
  □(i : φ) ∈ ⦃γ⦄ → φ ∈ ⦃γ⦄ :=
begin
  intros a, induction γ, 
  case atom_prop { simp at *, exfalso, exact a }, 
  case perp { simp at *, exfalso, exact a },
  case imply {
    simp at *, cases a, 
    { right, left, exact γ_ih_a a },
    { right, right, exact γ_ih_a_1 a }
  },
  case box {
    simp at *, cases a, 
    { right, rewrite a.right, apply used_self },
    { right, exact γ_ih a }
  },
  case announce {
    simp at *, cases a,
    { right, left, exact γ_ih_a a },
    { right, right, exact γ_ih_a_1 a }
  }
end

end pal_logic

