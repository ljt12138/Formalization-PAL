-- Copyright (C) 2020 by @ljt12138

import tactic pal.basics

namespace pal_logic 

/-----------------------------------------------------------------------
 -                    Reduction of Dynamic Modality                    -
 -----------------------------------------------------------------------

   Now we have define the syntax and semantics for PAL⬝S5, in which the 
public announcement [!φ] is called dynamic modaltiy. Here we will show 
that a PAL⬝S5 sentence can be translate to an equivalent static S5 
sentence. The idea is to use the following axioms recursively.
          
                 [!φ]p          ≡         φ → p
                 [!φ]⊥          ≡         φ → ⊥
                 [!φ](ψ→γ)      ≡         [!φ]ψ → [!φ]γ
                 [!φ]□ᵢψ        ≡         φ → □ᵢ[!φ]ψ
  
  Our plan is to show the soundness of the axioms, prove some lemma about
semantically equivalent, and then prove our main theorem.
-/

/-     ---- 1. Semantically Equivalent and Recursion Axioms ----      -/

inductive static {α agent : Type} : sentence α agent → Prop 
| atom (p : _)                : static ⟦p⟧
| perp                        : static ⊥
| imply (φ ψ : _)             : static φ → static ψ → static (φ ↣ ψ)
| box (a : _) (φ : _)         : static φ → static □(a : φ) 

@[simp]
def sem_equiv {α agent : Type} (φ φ' : sentence α agent) := 
  ∀ W : Type, ∀ M (s : W), (M, s) ⊨ φ ↔ (M, s) ⊨ φ'

infix ≡ := sem_equiv

@[simp, refl]
lemma sem_equiv_refl {α agent : Type} (φ : sentence α agent) :
  φ ≡ φ :=
begin
  unfold sem_equiv, intros, trivial
end

@[symm]
lemma sem_equiv_symm {α agent : Type} (φ ψ : sentence α agent) : 
  φ ≡ ψ → ψ ≡ φ := 
begin
  unfold sem_equiv, intros, symmetry, apply a
end

@[trans]
lemma sem_equiv_trans {α agent : Type} (φ ψ γ : sentence α agent) : 
  φ ≡ ψ → ψ ≡ γ → φ ≡ γ := 
begin
  unfold sem_equiv, intros a a' W M s, 
  have a₁ := a W M s, 
  have a₂ := a' W M s, 
  tauto
end

lemma recursion_atom {α agent : Type} : ∀ (p : α) (φ : sentence α agent), 
  ([!φ]⟦p⟧) ≡ φ ↣ ⟦p⟧ :=
begin
  intros, unfold sem_equiv, intros, split,
  { intros a, simp at *, exact a },
  { intros a, simp at *, exact a }
end

lemma recursion_perp {α agent : Type} : ∀ (φ : sentence α agent), 
  ([!φ]⊥) ≡ φ ↣ ⊥ :=
begin
  intros, unfold sem_equiv, intros, split,
  { intros a, simp at *, exact a},
  { intros a, simp at *, exact a}
end

lemma recursion_imply {α agent : Type} : ∀ (φ ψ γ : sentence α agent), 
  ([!φ]ψ↣γ) ≡ ([!φ]ψ) ↣ ([!φ]γ) := 
begin
  intros, unfold sem_equiv, intros, split,
  { 
    intros a, unfold evaluate at *, intros a₁ a₂, 
    apply a, exact a₂, exact a₁ a₂
  },
  {
    intros a, unfold evaluate at *, intros a₁ a₂, 
    apply a, intros, exact a₂, exact a₁
  }
end

lemma recursion_box {α agent : Type} : ∀ (i : agent) (φ ψ : sentence α agent),
  ([!φ]□(i : ψ)) ≡ φ ↣ □(i : [!φ]ψ) :=
begin
  intros, unfold sem_equiv, intros, split,
  {
    intros a, unfold evaluate at *, intros a₁ t a₂ a₃, 
    apply a, exact a₁, simp, 
    right, tauto
  },
  {
    intros a, unfold evaluate at *, intros a₁ t a₂,
    apply a,  { exact a₁ }, 
    { 
      simp at a₂, cases a₂,
      { rewrite a₂, cases M.equiv i, apply left },
      { tauto } 
    },
    { 
      simp at a₂, cases a₂, 
      { rewrite ← a₂, exact a₁ },
      { tauto }
    }
  }
end

lemma equiv_imply {α agent : Type} {φ ψ φ' ψ' : sentence α agent} : 
  φ ≡ φ' → ψ ≡ ψ' → φ ↣ ψ ≡ φ' ↣ ψ' :=
begin
  intros a₁ a₂, unfold sem_equiv, intros, split,
  { simp, intros a₃ a₄, apply (a₂ _ _ _).mp, apply a₃, apply (a₁ _ _ _).mpr, exact a₄ },
  { simp, intros a₃ a₄, apply (a₂ _ _ _).mpr, apply a₃, apply (a₁ _ _ _).mp, exact a₄ }
end

lemma equiv_box {α agent : Type} {i : agent} {φ ψ : sentence α agent} :
  φ ≡ ψ → □(i : φ) ≡ □(i : ψ) :=
begin
  intros, unfold sem_equiv, intros, split,
  { intros, unfold evaluate at *, intros, apply (a W M t).mp, exact a_1 t a_2 },
  { intros, unfold evaluate at *, intros, apply (a W M t).mpr, exact a_1 t a_2}
end

lemma equiv_restriction {α agent W : Type} (M : worlds α agent W) (P P' : W → Prop) :
  (∀ t, P t ↔ P' t) → (restriction M P = restriction M P') :=
begin
  intros a, simp, 
  have a' : ∀ t, P t = P' t, intros, apply propext, apply a,
  repeat {apply funext, intros},
  simp, rewrite a', rewrite a'
end

lemma equiv_announce {α agent : Type} {φ ψ φ' ψ' : sentence α agent} : 
  φ ≡ φ' → ψ ≡ ψ' → ([!φ]ψ) ≡ [!φ']ψ' :=
begin
  intros a₁ a₂, unfold sem_equiv, intros, split,
  { 
    intros, unfold evaluate at *, intros a', apply (a₂ _ _ _).mp, 
    rewrite equiv_restriction, 
    { apply a, apply (a₁ _ _ _).mpr, exact a' },
    { intros, symmetry, exact a₁ _ _ _ }
  },
  {
    intros, unfold evaluate at *, intros a', apply (a₂ _ _ _).mpr, 
    rewrite equiv_restriction, 
    { apply a, apply (a₁ _ _ _).mp, exact a' },
    { intros, exact a₁ _ _ _ }
  }
end

/-                   ---- 2. Main Theorem ----                   -/

lemma reduction_lemma {α agent : Type} (φ ψ : sentence α agent) : 
  static φ → static ψ → ∃ γ, ([!φ]ψ) ≡ γ ∧ static γ :=
begin
  intros a₁ a₂, induction a₂ with p ψ₁ ψ₂ a₂' a₂'' ih₁ ih₂ i ψ a_ψ ih₁, 
  { 
    existsi φ↣⟦p⟧, split, apply recursion_atom, 
    apply static.imply, assumption, apply static.atom 
  },
  {
    existsi φ↣⊥, split, apply recursion_perp, 
    apply static.imply, assumption, apply static.perp
  },
  {
    cases ih₁ with γ₁ ih₁, cases ih₂ with γ₂ ih₂, 
    existsi γ₁ ↣ γ₂, split,
    { 
      have h₁ := recursion_imply φ ψ₁ ψ₂,
      have h₂ : ([!φ]ψ₁) ↣ ([!φ]ψ₂) ≡ γ₁ ↣ γ₂, 
        { apply equiv_imply, exact ih₁.left, exact ih₂.left },
      transitivity, assumption, assumption
    },
    { apply static.imply, exact ih₁.right, exact ih₂.right }
  },
  {
    cases ih₁ with γ ih₁, cases ih₁ with ih₁ ih₂, 
    existsi φ ↣ □(i : γ), split,
    {
      have h₁ := recursion_box i φ ψ, 
      have h₂ : φ↣□(i:[!φ]ψ) ≡ φ↣□(i:γ), 
        { apply equiv_imply, simp, apply equiv_box, exact ih₁ },
      transitivity, assumption, assumption
    }, 
    { apply static.imply, exact a₁, apply static.box, exact ih₂ }
  }
end

theorem reduction_dynamics {α agent : Type} (φ : sentence α agent) :
  ∃ ψ, φ ≡ ψ ∧ static ψ :=
begin
  induction φ with p φ₁ φ₂ ih₁ ih₂ i φ ih φ₁ φ₂ ih₁ ih₂,
  { existsi ⟦p⟧, split, simp, apply static.atom },
  { existsi (⊥ : sentence α agent), split, simp, apply static.perp },
  {
    cases ih₁ with ψ₁ ih₁, cases ih₂ with ψ₂ ih₂, existsi ψ₁ ↣ ψ₂, split,
    { exact equiv_imply ih₁.left ih₂.left },
    { apply static.imply, tauto, tauto }
  },
  {
    cases ih with φ' ih, existsi □(i : φ'), split,
    { exact equiv_box ih.left },
    { apply static.box, exact ih.right }
  },
  {
    cases ih₁ with ψ₁ ih₁, cases ih₂ with ψ₂ ih₂,
    cases reduction_lemma ψ₁ ψ₂ ih₁.right ih₂.right with γ h,
    existsi γ, split,
    { 
      have a := equiv_announce ih₁.left ih₂.left,
      transitivity, exact a, exact h.left
    },
    { exact h.right }
  }
end

end pal_logic

