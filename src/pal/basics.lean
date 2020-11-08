-- Copyright (C) 2020 by @ljt12138

import tactic

namespace pal_logic 

inductive sentence (α : Type) (agent : Type) : Type 
| atom_prop : α → sentence                          -- atomic propositions
| perp : sentence                                   -- contradiction ⊥
| imply : sentence → sentence → sentence            -- imply u v     := u → v
| box : agent → sentence → sentence                 -- box a v       := □ₐ v
| announce : sentence → sentence → sentence         -- announce a v  := [!a] v

notation `⟦` p `⟧`        := sentence.atom_prop p
notation `⊥`              := sentence.perp  
notation `□(` a `:` p `)` := sentence.box a p
notation `[!` a `]` v     := sentence.announce a v
infixr `↣`:55             := sentence.imply
notation `◇(` a `:` p `)` := (□(a : p ↣ ⊥) ↣ ⊥)

@[simp] def mo_and {α agent : Type} (φ ψ : sentence α agent) := (φ ↣ (ψ ↣ ⊥)) ↣ ⊥ 
infixr `&`:60             := mo_and

structure worlds (α agent W : Type) : Type := 
(f : W → α → Prop)
(view : agent → W → W → Prop)
(equiv : ∀ (a : agent), equivalence (view a))

def model (α agent W : Type) := worlds α agent W × W

@[simp]
def restriction {a agent W : Type} 
  (M : worlds a agent W) (P : W → Prop) : worlds a agent W := 
{
  f := M.f,
  view := λ a t t', t = t' ∨ (P t ∧ P t' ∧ M.view a t t'),
  equiv := 
    begin
      intros a', unfold equivalence, 
      cases M.equiv a' with ref tmp, 
      cases tmp with sym tra,
      split,
      { unfold reflexive, intros, left, simp }, split,  
      { 
        unfold symmetric, intros, cases a_1,
        { left, rewrite a_1 }, 
        { right, split, tauto, split, tauto, apply sym, tauto },
      },
      {
        unfold transitive, intros, cases a_1, 
        { 
          cases a_2, 
          { left, rewrite a_1, assumption},
          { rewrite a_1, right, assumption }
        }, 
        {
          cases a_2, 
          { rewrite ← a_2, right, assumption },
          { right, split, tauto, split, tauto, fapply tra, exact y, tauto, tauto }
        }
      }
    end
}

@[simp]
def evaluate {α agent W : Type} : model α agent W → sentence α agent → Prop 
| (M, s) ⟦p⟧              := M.f s p
| (M, s) ⊥                := false
| (M, s) (φ ↣ ψ)          := evaluate (M, s) φ → evaluate (M, s) ψ
| (M, s) □(a : p)         := ∀ t, M.view a s t → evaluate (M, t) p
| (M, s) [!φ]ψ            := evaluate (M, s) φ → 
                             evaluate ((restriction M (λ t, evaluate (M, t) φ)), s) ψ

infix `⊨`:30 := evaluate

@[simp]
def tautology {α agent : Type} (φ : sentence α agent) :=
  ∀ (W : Type) M (s : W), (M, s) ⊨ φ

prefix `⊨`:35 := tautology

variables (α agent : Type) (φ : sentence α agent)

end pal_logic

