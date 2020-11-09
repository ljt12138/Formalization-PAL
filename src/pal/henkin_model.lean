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

/-               ---- 1. Definitions and Lemmas ----                    -/

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

lemma ext_origin {α agent : Type} {d : decider α agent} {φ : sentence α agent} :
  ∀ ψ, d ψ → (ext d φ) ψ := 
begin
  intros, right, exact a
end

lemma ext_new {α agent : Type} {d : decider α agent} {φ : sentence α agent} : 
  ext d φ φ :=
begin
  left, refl
end

-- firstly, show that Δ ∪ {φ} ⊢ ⊥ implies that Δ ⊢ ¬φ, 
--  then, in the case ¬φ ∈ Γ and φ ∈ Γ', we have Δ ⊢ φ and Δ ⊢ ¬φ, hence Δ ⊢ ⊥, 
--  contradiction

private def single_extend {α agent : Type} (d : decider α agent) (φ : sentence _ _) := 
begin 
  classical,
  exact if (consistent_set (ext d φ)) then ext d φ else ext d (φ ↣ ⊥)
end

private def henkin_enum {α agent : Type} [encodable (sentence α agent)]
        (d₀ : decider α agent) : ℕ → decider α agent 
| 0         := d₀
| (n + 1)   := let d := henkin_enum n in 
                 match encodable.decode (sentence α agent) n with 
                 | none        := d
                 | some φ      := single_extend d φ
                 end

lemma extend_preserve {α agent : Type} (d : decider α agent) (φ ψ : sentence _ _) :
  d ψ → consistent_set d → single_extend d φ ψ :=
begin
  intros h₁ h₂,
  cases em (consistent_set (ext d φ)), 
  { 
    simp [single_extend, h], cases em (φ = ψ),
    { rewrite h_1, apply ext_new },
    { apply ext_origin, exact h₁ } 
  },
  {
    simp [single_extend, h], cases em (φ↣⊥ = ψ),
    { rewrite h_1, apply ext_new },
    { apply ext_origin, exact h₁ } 
  }
end

lemma extend_new {α agent : Type} (d : decider α agent) (φ : sentence _ _) :
  single_extend d φ φ ∨ single_extend d φ (φ↣⊥) :=
begin
  cases em (consistent_set (ext d φ)),
  { simp [single_extend, h], left, apply ext_new },
  { simp [single_extend, h], right, apply ext_new }
end

lemma dsingle_extension {α agent : Type} (d : decider α agent) (φ : sentence _ _) :
  consistent_set d → let d' := single_extend d φ 
    in consistent_set d' ∧ (∀ ψ, d ψ → d' ψ) ∧ (d' φ ∨ d' (φ↣⊥)) :=
begin
  intros h₁,
  cases classical.em (consistent_set (ext d φ)),
  { -- d ∪ {φ} is consistent 
    split, 
    { simp [single_extend, h], exact h },
    { 
      simp [single_extend, h, ext], split,
      { intros ψ h', right, exact h' },
      { left, left, refl }
    }
  },
  { -- d ∪ {φ} is inconsistent
    split, 
    { 
      simp [single_extend, h₁, h], 
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
      simp [single_extend, h], split,
      { apply ext_origin },
      { right, apply ext_new }
    }
  }
end

private def prefix_decider {α agent : Type} [encodable (sentence α agent)] 
  (d : decider α agent) (n : ℕ) := ∀ φ, encodable.encode φ < n →  d φ ∨ d (φ ↣ ⊥)
 
lemma henkin_enum_consistent {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) (n : ℕ) : 
    consistent_set (henkin_enum d₀ n) :=
begin
  induction n with n ih,
  { exact h },
  {
    unfold henkin_enum, 
    have ht : ∃ pφ, pφ = encodable.decode (sentence α agent) n, 
    { existsi _, refl }, 
    cases ht with φ ref, rewrite ← ref, cases φ,
    { simp [henkin_enum], exact ih },
    { simp [henkin_enum], exact (dsingle_extension _ φ ih).left }
  }
end

lemma henkin_enum_prefix {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) (n : ℕ) : 
    prefix_decider (henkin_enum d₀ n) n := 
begin
  induction n with n ih,
  { simp [prefix_decider, henkin_enum] },
  {
    simp [prefix_decider, henkin_enum], 
    have ht : ∃ pφ, pφ = encodable.decode (sentence α agent) n, 
    { existsi _, refl },
    cases ht with pφ ref, rewrite ← ref, cases pφ with φ,
    { -- [φ] = n
      simp [henkin_enum], intros ψ a, 
      have ht : encodable.encode ψ ≤ n := by omega,
      cases lt_or_eq_of_le ht with h₁ h₁, 
      { apply ih, exact h₁ },
      { rewrite ← h₁ at ref, simp at ref, exfalso, exact ref }
    },
    { -- [φ] < n
      simp [henkin_enum], intros ψ a,
      have ht : encodable.encode ψ ≤ n := by omega,
      cases lt_or_eq_of_le ht with h₁ h₁, 
      {
        unfold prefix_decider at ih,
        cases ih ψ h₁ with h₂ h₂, 
        { 
          left, apply extend_preserve, exact h₂, 
          apply henkin_enum_consistent, exact h,   
        },
        {
          right, apply extend_preserve, exact h₂,
          apply henkin_enum_consistent, exact h
        }
      },
      {
        rewrite ← h₁ at ref, simp at ref, rewrite ref, 
        apply extend_new
      }
    }
  }
end 

lemma henkin_enum_subset {α agent : Type} [encodable (sentence α agent)] 
  (d₀ : decider α agent) (h : consistent_set d₀) (n m : ℕ) (φ : sentence α agent) : 
    (n ≤ m) → (henkin_enum d₀ n) φ → (henkin_enum d₀ m) φ :=
begin
  intros h₁ h₂,
  induction m with m ih,
  { have ht : n = 0 := by omega, rewrite ht at h₂, exact h₂ },
  {
    cases lt_or_eq_of_le h₁ with h₃ h₃,
    {
      simp [henkin_enum],
      have ht : ∃ pφ, pφ = encodable.decode (sentence α agent) m, 
      { existsi _, refl },
      cases ht with pφ h₃, rewrite ← h₃, cases pφ with ψ,
      { simp [henkin_enum], apply ih, omega},
      { 
        simp [henkin_enum], apply extend_preserve, apply ih, omega, 
        apply henkin_enum_consistent, exact h 
      }
    },
    { rewrite ← h₃, exact h₂ }
  }
end

lemma henkin_enum_em {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent)(φ : sentence α agent) :
    henkin_enum d₀ (encodable.encode φ + 1) φ 
      ∨ henkin_enum d₀ (encodable.encode φ + 1) (φ↣⊥) :=
begin
  simp [henkin_enum],
  cases em (consistent_set (ext (henkin_enum d₀ (encodable.encode φ)) φ)),
  { simp [single_extend, h], left, apply ext_new },
  { simp [single_extend, h], right, apply ext_new }
end
    
def henkin_union {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (φ : sentence α agent) :=
    henkin_enum d₀ ((encodable.encode φ) + 1) φ

lemma henkin_union_subset {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) (φ : sentence _ _) :
    d₀ φ → henkin_union d₀ φ :=
begin
  intros h₁, unfold henkin_union, 
  apply henkin_enum_subset _ h 0, simp, 
  simp [henkin_enum], exact h₁
end

def maximum_encoding {α agent : Type} [encodable (sentence α agent)] 
  : list (sentence α agent) → ℕ 
| []     := 0
| (φ::Γ) := max (encodable.encode φ + 1) (maximum_encoding Γ) 

lemma henkin_union_Γ {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) (Γ : list (sentence α agent)) :
    (∀ φ, φ ∈ Γ → henkin_union d₀ φ) → 
    (∀ φ, φ ∈ Γ → henkin_enum d₀ (maximum_encoding Γ) φ) :=
begin
  intros h₁ φ h₂,
  induction Γ with ψ Γ ih,
  { simp at h₂, exfalso, exact h₂ },
  { 
    simp [maximum_encoding], simp at h₂, cases h₂,
    {
      rewrite h₂ at *,
      have ht := h₁ ψ (list.mem_cons_self _ _), simp [henkin_union] at ht,
      apply henkin_enum_subset, exact h, apply le_max_left, exact ht
    },
    { 
      apply henkin_enum_subset, exact h, apply le_max_right, apply ih,
      intros ρ h₃, apply h₁, simp, right, exact h₃, exact h₂
    }
  }
end

lemma henkin_union_consistent {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) : 
    consistent_set (henkin_union d₀) :=
begin
  intros Γ h₁ contra,
  apply (henkin_enum_consistent d₀ h),
  apply henkin_union_Γ, exact h, 
  exact h₁, exact contra
end

lemma henkin_enum_agree {α agent : Type} [encodable (sentence α agent)] 
  (d₀ : decider α agent) (h : consistent_set d₀) (φ : sentence α agent) (n : ℕ) :
    henkin_enum d₀ n φ → henkin_enum d₀ (encodable.encode φ + 1) φ :=
begin
  intros h₁, classical, by_contra h₂,
  have ht : henkin_enum d₀ (encodable.encode φ + 1) (φ ↣ ⊥),
  { 
    have ht' := henkin_enum_em d₀ φ,
    cases ht', exfalso, exact h₂ ht',
    exact ht'
  },
  have ht₁ := henkin_enum_subset d₀ h n (max n (encodable.encode φ + 1)) φ (le_max_left _ _) h₁, 
  have ht₂ := henkin_enum_subset d₀ h _ (max n (encodable.encode φ + 1)) (φ↣⊥) (le_max_right _ _) ht, 
  apply henkin_enum_consistent d₀ h (max n (encodable.encode φ + 1)) [φ, φ↣⊥],
  intros ψ, 
  { intros a, simp at a, cases a, repeat {rewrite a, assumption} },
  {
    unfold conjunction, 
    apply uncurry, existsi proof.ax2' _, prover 
  }
end

lemma henkin_union_maximal {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) : 
    ∀ φ, henkin_union d₀ φ ∨ henkin_union d₀ (φ ↣ ⊥) :=
begin
  intros φ, 
  cases em (henkin_union d₀ φ) with h₁ h₁, 
  { exact or.inl h₁ },
  { 
    right, unfold henkin_union at *, 
    have ht₂ : henkin_enum d₀ (encodable.encode φ + 1) (φ ↣ ⊥),
    {  
      have ht₃ := henkin_enum_em d₀ φ,
      cases ht₃, 
      { exfalso, exact h₁ ht₃ },
      { exact ht₃ }
    },
    apply henkin_enum_agree, repeat {assumption}
  }
end

lemma henkin_union_consistent_decider {α agent : Type} [encodable (sentence α agent)]
  (d₀ : decider α agent) (h : consistent_set d₀) :
    consistent_decider (henkin_union d₀) :=
begin
  unfold consistent_decider, split,
  { apply henkin_union_consistent, exact h }, 
  { apply henkin_union_maximal, exact h }
end

theorem dcomplete_extension {α agent : Type} [encodable (sentence α agent)] :
  ∀ d : decider α agent, consistent_set d → 
    ∃ d' : decider_world α agent, (∀ φ, d φ → decides d' φ) :=
begin
  intros d₀ h, 
  have ht := henkin_union_consistent_decider d₀ h, 
  existsi (decider_world.mk (henkin_union d₀) ht),
  intros φ h₁, simp, apply henkin_union_subset, exact h, exact h₁
end

/-                ----4. Correctness of Henkin model----              -/

theorem henkin_correctness {α agent : Type} [encodable (sentence α agent)]:
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

