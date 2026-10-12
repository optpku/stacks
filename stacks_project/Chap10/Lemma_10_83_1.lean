/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Finiteness.Projective.Flat
import StacksCheckRecall

/-!
# Finite projective modules

@stack 058R

Finite projectivity is canonically owned by `Module.FiniteProjective`; the source conjunction
`Module.Finite R M ∧ Module.Projective R M` is its reducible definition.  The chapter entry is
therefore a typed recall of the shared characterization rather than a second theorem name.
-/

@[expose] public section

universe u v

/- Lemma 10.83.1 (Tag 058R): an `R`-module is finite projective if and only if it is finitely
presented and flat. -/
@[stacks 058R]
#check (@Module.FiniteProjective.iff_finitePresentation_and_flat :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    (Module.Finite R M ∧ Module.Projective R M) ↔
      Module.FinitePresentation R M ∧ Module.Flat R M)

#check @Module.FiniteProjective.finitePresentation
#check @Module.FiniteProjective.flat
#check @Module.FiniteProjective.of_finitePresentation_of_flat
