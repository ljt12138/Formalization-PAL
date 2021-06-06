# Formalization of PAL

We present a formalization of PAL+modal logic S5 in Lean, as an experiment to formalize logic systems in proof assistant. Intuitively speaking, PAL extends modal logic S5 with public announce ment modality [!φ]ψ, that means that *after φ is announced, ψ is true*.

This formalization contains two parts.
- **Recursion Theorem for PAL**.  Any PAL sentence can be translated to a sentence without public announce modality. 
- **Completeness of S5**. Any tautology of S5 can be proved through our Hilbert-style system.

## File Structure 

### Main Result

In `src/pal/` we present our formalization of PAL. 
- `basics.lean` contains definition of syntax and semantics of PAL. 
- `proof.lean` contains a sound and complete proof system for modal logic S5 (without public announcement modality), and an automatic proof check meta-algorithm.
- `dynamic.lean` contains a proof of **Recursion Theorem for PAL**. 
- `soundness.lean` verifies that the proof system for S5 is sound. 
- `lemmas.lean` contains lemmas about proof system and semantics for completeness proof.
- `henkin_model` contains the main part of the completeness proof, which shows that (1) we can extend a consistent set to a maximal consistent set and (2) all maximal consistent sets form a proper model. 
- `completeness.lean` proves the completeness theorem via the construction above.

### Propositional Logic

In `src/propositional` we present our formalization of propositional logic, which is only for experiment. Our completeness proof for propositional logic is much more robust: it does not require any property of the type of atomic propositions (i.e. the proof holds even if there are uncountably many atomic propositions). 
- `basics.lean` defines the syntax, semantics and proof system for propositional logic. 
- `thms.lean` contains basic results about proof systems and semantics.
- `soundness.lean` verifies the soundness of proof system. 
- `used_formula.lean` provides a procedure to collect all sub-formalas of a set of formula.
- `complete_extension.lean` provides a way to extend a consistent set to a maximal one. 
- `completeness.lean` proves the completeness theorem via the construction above.

## Dependency

The entire proof is type-checked with Lean 3.20. If `mathlib` is not globally installed, one may need to run `leanproject add-mathlib` to compile this proof.  

