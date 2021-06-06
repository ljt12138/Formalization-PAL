import tactic pal.basics pal.dynamic

namespace pal_logic 

def pal_reduce1 {α agent : Type} (ϕ : sentence α agent) : 
  sentence α agent → sentence α agent 
| ⟦p⟧      := ϕ ↣ ⟦p⟧ 
| ⊥       := ϕ ↣ ⊥
| (ψ ↣ γ) := (pal_reduce1 ψ) ↣ (pal_reduce1 γ)
| □(i:ψ)   := ϕ ↣ □(i : (pal_reduce1 ψ)) 
| [!ψ]γ    := ⊥

def pal_reduce {α agent : Type} : 
  sentence α agent → sentence α agent 
| ⟦p⟧      := ⟦p⟧ 
| ⊥       := ⊥
| (ψ ↣ γ) := (pal_reduce ψ) ↣ (pal_reduce γ)
| □(i:ψ)   := □(i : pal_reduce ψ) 
| [!ψ]γ    := pal_reduce1 (pal_reduce ψ) (pal_reduce γ)

lemma reduction1_static {α agent : Type} (ϕ ψ : sentence α agent) : 
    static ϕ → static ψ → static (pal_reduce1 ϕ ψ) := 
begin
  intros a₁ a₂,
  induction ψ,
  { unfold pal_reduce1, apply static.imply, assumption, assumption },
  { unfold pal_reduce1, apply static.imply, assumption, assumption },
  {
    unfold pal_reduce1 at *, cases a₂, apply static.imply, 
    tauto, tauto
  },
  {
    unfold pal_reduce1 at *, cases a₂, apply static.imply,
    tauto, apply static.box, tauto
  },
  {
    unfold pal_reduce1 at *, apply static.perp
  }
end

lemma reduction1_sound {α agent : Type} (ϕ ψ : sentence α agent) : 
    static ψ → ([!ϕ]ψ) ≡ pal_reduce1 ϕ ψ := 
begin
  intros st,
  induction ψ, 
  { unfold pal_reduce1 sem_equiv, tauto },
  { unfold pal_reduce1 sem_equiv, tauto },
  {
    cases st,
    unfold pal_reduce1 sem_equiv at *, 
    intros W M s, split,
    { 
      intros a₁ a₂,
      apply (ψ_ih_a_1 st_a_1 W M s).mp,
      apply (recursion_imply ϕ ψ_a ψ_a_1 W M s).mp a₁,
      exact (ψ_ih_a st_a W M s).mpr a₂
    },
    {
      intros a₁,
      apply (recursion_imply ϕ ψ_a ψ_a_1 W M s).mpr,
      intros a₂,
      apply (ψ_ih_a_1 st_a_1 W M s).mpr,
      apply a₁,
      exact (ψ_ih_a st_a W M s).mp a₂
    }
  },
  {
    cases st,
    unfold pal_reduce1 sem_equiv at *,
    intros W M s, split,
    {
      intros a₁ a₂ t a₃,
      apply (ψ_ih st_a_1 W M t).mp, 
      exact ((recursion_box ψ_a ϕ ψ_a_1 W M s).mp a₁ a₂ _ a₃)
      -- rewrite ← (iff.to_eq (recursion_box ψ_a ϕ (pal_reduce1 ϕ ψ_a_1) W M s)),
    },
    {
      intros a₁, 
      apply (recursion_box ψ_a ϕ ψ_a_1 W M s).mpr,
      intros a₂ t a₃,
      apply (ψ_ih st_a_1 W M t).mpr,
      exact a₁ a₂ t a₃   
    }
  },
  { cases st }
end  

lemma reduction_sound {α agent : Type} (ϕ : sentence α agent) : 
    pal_reduce ϕ ≡ ϕ ∧ static (pal_reduce ϕ)  := 
begin 
  induction ϕ, 
  { split, unfold pal_reduce, apply static.atom },
  { split, unfold pal_reduce, apply static.perp },
  { 
    unfold pal_reduce, cases ϕ_ih_a, cases ϕ_ih_a_1, split, 
    { apply equiv_imply, assumption, assumption },
    { apply static.imply, assumption, assumption }
  },
  { 
    unfold pal_reduce, cases ϕ_ih, split,
    { apply equiv_box, assumption }, 
    { apply static.box, assumption }
  },
  {
    unfold pal_reduce, cases ϕ_ih_a, cases ϕ_ih_a_1, split,
    {
      apply sem_equiv_trans,
      { apply sem_equiv_symm, apply reduction1_sound, assumption },
      { apply equiv_announce, assumption, assumption }
    },
    {
      apply reduction1_static,
      assumption, assumption
    }
  }
end

end pal_logic