-- Copyright (C) 2020 by @ljt12138

import tactic pal.proof pal.basics pal.lemmas pal.dynamic

namespace pal_logic

/-----------------------------------------------------------------------
 -                          Henkin Model                               -
 -----------------------------------------------------------------------

  The Henkin model for modal logic is the tuple (W, ∼ᵢ, s, Vₛ), where 
 1. W is all maximal consistent set;
 2. u ∼ᵢ v iff for all □ᵢφ ∈ u, we have φ ∈ v;
 3. s ∈ W is current world;
 4. Vₛ ⊨ φ iff φ ∈ s.

  Since we are using type inside of set, we will call a set of sentences
a decider, and call a maximal consistent set a consistent decider. The 
following lemmas give some properties of consistent decider. 
 - decide_mp :: if (φ→ψ) ∈ Δ and φ ∈ Δ, then ψ ∈ Δ
 - decide_not_iff_not_decide :: φ ∉ Δ iff ¬φ ∈ Δ
 - decide_tauto :: if φ is a tautology, φ ∈ Δ
 - decide_and_iff_and_decide :: φ∧ψ ∈ Δ iff φ ∈ Δ and ψ ∈ Δ
 - decide_useless_condition :: if ψ ∈ Δ, then φ→ψ ∈ Δ 
 - decide_false_condition :: if φ ∉ Δ, then φ→ψ ∈ Δ

  These lemmas are used to show that the Henkin model is actually a 
model for modal logic S5, that is reflexive, transitive and symmetric. 

  The only hard part remained for our main theorem
                     φ ∈ s   iff   (M, s) ⊨ φ
is to deal with the case (φ = □ᵢψ). If (M, s) ⊨ φ holds, it is not 
trivial that φ ∈ s holds. We will prove this as following: consider the
set of sentences Δ = {¬ψ} ∪ {α | □ᵢα ∈ s}. 
 1. If Δ is inconsistent, we know that there exists α₁ α₂ ... αₙ ∈ Δ
    such that α₁∧α₂∧...∧αₙ∧¬ψ → ⊥ is provable, hence
                            ∧ₖαₖ → ψ
    is also provable. By axiom we have □ᵢ(∧ₖαₖ → ψ) provable, by 
    modality distribution we have □ᵢ(∧ₖαₖ) → □ᵢψ provable. Since αₖ ∈ Δ, 
    by definition we have □ᵢαₖ ∈ s for every k, by decide_mp we know that 
                          φ = □ᵢψ ∈ s. 
 2. If Δ is consistent, assume that everything is encodable, we may extend
    it to a consistent decider t (this is the Main Lemma we need). Then, 
    we will see that s ∼ᵢ t by definition, but ¬ψ ∈ t, contradiction to
    (M, s) ⊨ □ᵢψ. 

  The Main Lemma will be explained more clearly in section 3.
-/

/-                ----1. Definitions and Lemmas----                     -/

def decider (α agent : Type) := sentence α agent → Prop
@[simp] def consistent_set {α agent : Type} (d : decider α agent) :=
  (∀ Γ : list (sentence α agent), (∀ φ, φ∈Γ → d φ) → ¬ ⊢ conjunction Γ ↣ ⊥)
@[simp] def consistent_decider {α agent : Type} (d : decider α agent) := 
  consistent_set d ∧ ∀ φ, d φ ∨ d (φ↣⊥)

inductive decider_world (α agent : Type) : Type
| mk (d : decider α agent) : consistent_decider d → decider_world
@[simp] def decides {α agent : Type} : decider_world α agent → sentence α agent → Prop 
| (decider_world.mk d h) φ := d φ 

lemma decide_mp {α agent : Type} (d : decider_world α agent) : 
  ∀ φ ψ, decides d (φ↣ψ) → decides d φ → decides d ψ := 
begin
  intros φ ψ a₁ a₂, classical,
  by_contra a₃, cases d with d h, simp at *, 
  have h₁ : d (ψ↣⊥), { cases h.right ψ, exfalso, exact a₃ h_1, assumption },
  have h₂ := h.left [ψ↣⊥,φ↣ψ,φ], 
  apply h₂, 
  { 
    intros, simp at a, cases a, 
    rewrite a, assumption, cases a, 
    repeat {rewrite a, assumption} 
  },
  unfold conjunction,
  have hψ : ⊢ (ψ↣⊥) & (φ↣ψ) & φ ↣ ψ, 
  {
    existsi proof.conjr _ _ _, apply proof_of.conjr, 
    apply proof_of.conjmp
  },
  have hnψ : ⊢ (ψ↣⊥) & (φ↣ψ) & φ ↣ (ψ↣⊥),
  {
    have ht := id_provable (ψ↣⊥), cases ht, 
    existsi proof.conjl _ _ _, prover
  },
  have hax : ⊢ Ax2 ((ψ↣⊥)&(φ↣ψ)&φ) ψ ⊥, { existsi proof.ax2 _ _ _, prover },
  cases hax, cases hψ, cases hnψ,
  existsi proof.mp (proof.mp _ _) _, prover
end

lemma decide_not_iff_not_decide {α agent : Type} (d : decider_world α agent) :
  ∀ φ, ¬ decides d φ ↔ decides d (φ ↣ ⊥) :=
begin
  intros φ, split, classical, 
  {
    intros a₁, by_contra a₂,
    cases d with d h,  
    cases h.right φ, exact a₁ h_1, exact a₂ h_1
  },
  { 
    intros a₁ a₂, 
    have h₁ := decide_mp _ _ _ a₁ a₂,
    cases d with d h₂, 
    simp at h₂, apply (h₂.left [⊥]), 
    simp, assumption, simp, apply id_provable
  }
end

lemma decide_tauto {α agent : Type} (d : decider_world α agent) :
  ∀ φ, ⊢ φ → decides d φ :=
begin
  intros φ a₁, classical, by_contra a₂,
  have ht := (decide_not_iff_not_decide d φ).mp a₂,
  cases d with d h,
  apply h.left [φ↣⊥], simp, assumption,
  simp, cases a₁, 
  have ht' := dni φ, cases ht',
  existsi proof.mp _ _, prover
end

lemma decide_and_iff_and_decide {α agent : Type} (d : decider_world α agent) :
  ∀ φ ψ, decides d (φ & ψ) ↔ decides d φ ∧ decides d ψ :=
begin
  intros φ ψ, classical, split,
  {
    intros a, split, 
    have h₁ : decides d ((φ & ψ)↣φ), 
    { apply decide_tauto, apply uncurry, existsi proof.ax1 _ _, prover },
    apply decide_mp, repeat {assumption},
    have h₂ : decides d ((φ & ψ)↣ψ),
    { apply decide_tauto, apply uncurry, apply useless_condition, apply id_provable},
    apply decide_mp, repeat {assumption}
  },
  {
    intros, 
    have h₁ : decides d (φ↣ψ↣φ&ψ), 
    { apply decide_tauto, apply curry, apply id_provable }, 
    apply decide_mp, apply decide_mp, assumption, repeat {tauto}
  }
end

lemma decide_useless_condition {α agent : Type} (d : decider_world α agent) : 
  ∀ φ ψ, decides d φ → decides d (ψ ↣ φ) :=
begin
  intros φ ψ a,
  apply decide_mp, 
  { apply decide_tauto, existsi proof.ax1 _ _, prover },
  { assumption }
end

lemma decide_false_condition {α agent : Type} (d : decider_world α agent) :
  ∀ φ ψ, ¬ decides d φ → decides d (φ↣ψ) :=
begin
  intros φ ψ a, 
  have h₁ : decides d (φ↣⊥),
  { 
    cases d with d h, cases h.right φ, 
    { simp at *, exfalso, exact a h_1 },
    { simp, assumption }
  },
  have h₂ : decides d (φ↣⊥↣ψ),
  {
    apply decide_useless_condition,
    apply decide_tauto, 
    apply explosion
  },
  have h₃ : decides d (Ax2 φ ⊥ ψ),
  { 
    apply decide_tauto, 
    existsi proof.ax2 _ _ _, prover
  },
  unfold Ax2 at h₃,
  apply decide_mp, apply decide_mp, repeat {assumption}
end

/-           ----2. Access relation ∼ᵢ and Henkin Model----              -/

@[simp] def access {α agent : Type} (i : agent) (s t : decider_world α agent) :=
  ∀ φ : sentence α agent, decides s □(i:φ) → decides t φ
  
notation s `∼{` i `}` t := access i s t

@[refl]
lemma access.reflexive {α agent : Type} (i : agent) (s t : decider_world α agent) :
  s ∼{i} s :=
begin
  simp, intros φ a,
  apply decide_mp, 
  { apply decide_tauto, existsi proof.ref _ _, apply proof_of.ref, exact i },
  { assumption }
end

@[trans]
lemma access.transitive {α agent : Type} (i : agent) (s t₁ t₂ : decider_world α agent) :
  (s ∼{i} t₁) → (t₁ ∼{i} t₂) → (s ∼{i} t₂) :=
begin
  simp, intros a₁ a₂,
  intros φ a₃, apply a₂, apply a₁,
  apply decide_mp,
  { apply decide_tauto, existsi proof.trans _ _, apply proof_of.trans },
  { assumption }
end

@[symm]
lemma access.symmetric {α agent : Type} (i : agent) (s t : decider_world α agent) :
  (s ∼{i} t) → (t ∼{i} s) :=
begin
  simp, intros a₁ φ a₂,
  have h₁ : decides s (□(i:φ)) ∨ decides s (□(i:φ)↣⊥),
  { cases s with s h, cases h.right _, left, assumption, right, assumption },
  cases h₁,
  {
    apply decide_mp, apply decide_tauto, 
    existsi proof.ref _ _, apply proof_of.ref, exact i,
    assumption
  },
  {
    exfalso,
    have h₂ : decides s (□(i:□(i:φ)↣⊥)), 
    { 
      apply decide_mp, apply decide_tauto,
      existsi proof.sym _ _, apply proof_of.sym, assumption
    },
    have h₃ := a₁ _ h₂,
    have h₄ : decides t ⊥, 
    { apply decide_mp, assumption, assumption }, 
    cases t with t h, 
    apply h.left [⊥], simp, assumption,
    simp, apply id_provable
  }
end

@[simp]
def henkin_worlds (α agent : Type) : worlds α agent (decider_world α agent) := 
{
  f := λ s a, decides s ⟦a⟧,
  view := access,
  equiv := 
  begin
    intros i, unfold equivalence reflexive symmetric transitive, split,
    { intros, apply access.reflexive }, split,
    { intros x y, apply access.symmetric }, 
    { intros x y z, apply access.transitive }
  end
}

@[simp]
def henkin_model {α agent : Type} (s : decider_world α agent) := 
  (henkin_worlds α agent, s)

notation `⦃` s `⦄` := henkin_model s

/-              ----3. Encoding and Complete Extension----            -/

-- Here we explicitly gives an encoding of sentences, 
--  provided that both α and agent are encodable
@[simp]
def enc {α agent : Type} (f : α → ℕ) (g : agent → ℕ) : sentence α agent → ℕ
| ⟦p⟧              := (nat.mkpair 1 (f p)) + 1
| ⊥                := (nat.mkpair 2 0) + 1
| (φ↣ψ)            := (nat.mkpair 3 (nat.mkpair (enc φ) (enc ψ))) + 1
| □(i : φ)         := (nat.mkpair 4 (nat.mkpair (g i) (enc φ))) + 1
| [!φ]ψ            := (nat.mkpair 5 (nat.mkpair (enc φ) (enc ψ))) + 1

@[simp]
def dec {α agent : Type} (f' : ℕ → option α) (g' : ℕ → option agent) 
    : ℕ → option (sentence α agent) 
| 0     := none
| (n+1) := have h₁ : n.unpair.snd < n+1 := 
             calc n.unpair.snd ≤ n   : nat.unpair_le_right _
                  ...          < n+1 : by simp,
           have h₂ : n.unpair.snd.unpair.fst < n+1 := 
             calc n.unpair.snd.unpair.fst ≤ n.unpair.snd : nat.unpair_le_left _
                  ...                     ≤ n            : nat.unpair_le_right _
                  ...                     < n+1          : by simp,
           have h₃ : n.unpair.snd.unpair.snd < n+1 :=
             calc n.unpair.snd.unpair.snd ≤ n.unpair.snd : nat.unpair_le_right _
                  ...                     ≤ n            : nat.unpair_le_right _
                  ...                     < n+1          : by simp,
           let op := n.unpair.fst,
               v  := n.unpair.snd in 
               match op with
               | 1 := match (f' v) with 
                      | some p := some ⟦p⟧
                      | none   := none
                      end
               | 2 := match v with
                      | 0      := some ⊥
                      | _      := none
                      end
               | 3 := let eφ := v.unpair.fst,
                          eψ := v.unpair.snd in
                          match dec eφ, dec eψ with
                          | none, _     := none
                          | _, none     := none
                          | some φ, some ψ := some (φ ↣ ψ)
                          end
               | 4 := let ei := v.unpair.fst,
                          eφ := v.unpair.snd in
                          match g' ei, dec eφ with
                          | none, _     := none
                          | _, none     := none
                          | some i, some φ := some □(i : φ)
                          end
               | 5 := let eφ := v.unpair.fst,
                          eψ := v.unpair.snd in
                          match dec eφ, dec eψ with
                          | none, _     := none
                          | _, none     := none
                          | some φ, some ψ := some [!φ]ψ
                          end
               | _ := none
               end

lemma sentence.encodable {α agent : Type} :
  encodable α → encodable agent → encodable (sentence α agent) :=
begin
  intros enc₁ enc₂, 
  cases enc₁ with f f' h₁, 
  cases enc₂ with g g' h₂,
  have h₃ : ∀ φ : sentence α agent, 
              dec f' g' (enc f g φ) = some φ, 
  {
    intros φ, induction φ,
    { simp, rewrite h₁, simp },
    { simp  },
    { simp, rewrite φ_ih_a, rewrite φ_ih_a_1, simp },
    { simp, rewrite φ_ih, rewrite h₂, simp },
    { simp, rewrite φ_ih_a, rewrite φ_ih_a_1, simp }
  },
  split, { exact h₃ }
end

private def ext {α agent : Type} (d : decider α agent) (φ : sentence _ _) := 
  λ ψ, ψ = φ ∨ d ψ

-- firstly, show that Δ ∪ {φ} ⊢ ⊥ implies that Δ ⊢ ¬φ, 
--  then, in the case ¬φ ∈ Γ and φ ∈ Γ', we have Δ ⊢ φ and Δ ⊢ ¬φ, hence Δ ⊢ ⊥, 
--  contradiction

lemma dsingle_extension {α agent : Type} (d : decider α agent) (φ : sentence _ _) :
  consistent_set d → ∃ d', consistent_set d' ∧ (∀ ψ, d ψ → d' ψ) ∧ (d' φ ∨ d' (φ↣⊥)) :=
begin
  intros h₁, 
  cases classical.em (consistent_set (ext d φ)),
  { -- d ∪ {φ} is consistent 
    existsi (ext d φ), split, exact h, split,
    { intros ψ h₂, simp [ext], right, exact h₂ },
    { simp [ext] }
  },
  { -- d ∪ {φ} is inconsistent
    existsi (ext d (φ↣⊥)), split, 
    { 
      unfold consistent_set, 
      intros Γ h₂ contra₁,
      apply h, intros Γ' h₃ contra₂,
      cases em (φ↣⊥ ∈ Γ),
      { 
        cases em (φ ∈ Γ'),
        { 
          cases contra_imp_conseq h_1 contra₁ with Γ₁, 
          cases contra_imp_conseq h_2 contra₂ with Γ₂,
          apply h₁ (Γ₁++Γ₂),
          { 
            intros ψ ht, simp at ht, cases ht,
            { 
              cases h₂ ψ (h_3.left ht),
              rewrite h_5 at *, exfalso, exact h_3.right.left ht, exact h_5
            },
            {
              cases h₃ ψ (h_4.left ht),
              rewrite h_5 at *, exfalso, exact h_4.right.left ht, exact h_5
            }
          },
          have ht₁ : Γ₁ ⊆ Γ₁ ++ Γ₂ := by simp, 
          have ht₂ : Γ₂ ⊆ Γ₁ ++ Γ₂ := by simp,
          cases conj_subset h_3.right.right ht₁, 
          cases conj_subset h_4.right.right ht₂,
          existsi proof.mp (proof.mp (proof.ax2 _ _ _) _) _,
          prover
        },
        {
          fapply h₁, exact Γ', 
          intros ψ h₄, 
          have ht := h₃ ψ h₄, simp [ext] at ht, cases ht, 
          { exfalso, apply h_2, rewrite ← ht, exact h₄ },
          { exact ht }, 
          exact contra₂
        }
      },
      {
        fapply h₁, exact Γ,
        intros ψ h₄, 
        have ht := h₂ ψ h₄, simp [ext] at ht, cases ht,
        { exfalso, apply h_1, rewrite ← ht, exact h₄ },
        { exact ht },
        exact contra₁
      }
    }, 
    { 
      split, intros, simp [ext], right, exact a,
      simp [ext]
    }
  }
end

theorem dcomplete_extension {α agent : Type} :
  ∀ d : decider α agent, consistent_set d → 
    ∃ d' : decider_world α agent, (∀ φ, d φ → decides d' φ) :=
begin
  sorry
end

/-                ----4. Correctness of Henkin model----              -/

theorem henkin_correctness {α agent : Type} :
  ∀ φ, static φ → ∀ s : decider_world α agent, (decides s φ ↔ ⦃s⦄ ⊨ φ) :=
begin
  intros φ st, 
  induction φ with p φ₁ φ₂ ih₁ ih₂ i φ ih,
  { intro s, cases s with s h, simp },
  {
    intro s, cases s with s h, simp, intros a, 
    apply h.left [⊥], simp, assumption,
    simp, apply id_provable
  },
  {
    intro s, cases st, 
    unfold henkin_model at *, split,
    {
      intros a₁, unfold evaluate, intros a₂,
      classical, by_contra a₃,
      have h₁ := (ih₁ st_a s).mpr a₂, 
      have h₂ := (decide_not_iff_not_decide _ _).mp 
                   (not_imp_not.mpr (ih₂ st_a_1 s).mp a₃),
      have ht : decides s ⊥, 
      { apply decide_mp, exact h₂, apply decide_mp, assumption, assumption },
      cases s with s h, 
      apply h.left [⊥], simp at *, assumption,
      simp, apply id_provable
    },
    {
      intros a₁, unfold evaluate at *, 
      cases (classical.em (decides s φ₁)),
      {
        classical, by_contra, 
        have h' := (ih₂ st_a_1 s).mpr (a₁ ((ih₁ st_a s).mp h)),
        have h₂ := (decide_not_iff_not_decide _ _).mp a,
        have ht : decides s ⊥,
        { apply decide_mp, exact h₂, apply decide_useless_condition, assumption },
        cases s with s h₁, 
        apply h₁.left [⊥], simp at *, assumption,
        simp, apply id_provable
      },
      {
        apply decide_false_condition,
        assumption
      }
    }
  },
  {
    intro s, cases st, split,
    {
      intros a₁ t a₂, 
      apply (ih st_a_1 _).mp,
      simp at a₂, apply a₂, exact a₁
    },
    {
      intros a₁, 
      have a₂ : ⦃s⦄ ⊨ φ, { apply a₁, apply access.reflexive, exact s },
      sorry
    }
  },
  { cases st }
end

end pal_logic

