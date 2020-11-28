-- Copyright (C) 2020 by @ljt12138

import tactic pal.henkin_model pal.soundness

namespace pal_logic

def trivial_world (α agent : Type) : worlds α agent ℕ := 
{
  f := λ s a, false, 
  view := λ i s t, s = t,
  equiv := 
  begin intros i, simp, apply eq_equivalence end
}

theorem completeness {α agent : Type} [encodable (sentence α agent)] 
  (φ : sentence α agent) : static φ → ⊨ φ → ⊢ φ :=
begin
  intros st h, classical, by_contra,
  have h₁ : consistent_set (λ ψ, ψ = φ↣⊥), 
  {
    simp, intros Γ h' contra, apply a,
    have h₂ : ⊢ conjunction [φ↣⊥] ↣ ⊥,
    {
      cases contra with pf pfh,
      existsi proof.conj Γ [φ↣⊥] ⊥ pf _, { prover },
      intros ψ h₁, rewrite h' _ h₁, simp
    },
    simp at h₂, cases h₂,
    existsi proof.mp (proof.ax3 _) _, prover
  },
  cases dcomplete_extension (λ ψ, ψ = φ↣⊥) h₁ with s h₂,
  have st' : static (φ↣⊥), 
  { apply static.imply, exact st, apply static.perp },
  have h₂ : ⦃s⦄ ⊨ φ ↣ ⊥,
  {
    apply (henkin_correctness (φ↣⊥) st' s).mp,
    apply h₂, reflexivity
  },
  simp at h₂, apply h₂, apply h
end 

end pal_logic
