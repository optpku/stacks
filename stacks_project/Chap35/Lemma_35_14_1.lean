/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FinitePresentation.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 35.14.1: finite presentation descends from a composite along a faithfully flat,
finitely presented second map. -/
@[stacks 02KK] #check
  (RingHom.FinitePresentation.of_comp_of_faithfullyFlat_of_finitePresentation :
    ∀ {R : Type u} {A : Type v} {B : Type w}
      [CommRing R] [CommRing A] [CommRing B]
      {f : R →+* A} {g : A →+* B},
      (g.comp f).FinitePresentation → g.FaithfullyFlat → g.FinitePresentation →
        f.FinitePresentation)
