/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.WeaklyAdmissible
import StacksCheckRecall

universe u

/- Lemma 87.4.9 -/
@[stacks 0DCZ] #check
  (TopologicalRing.Ideal.IsWeakIdealOfDefinition.henselianRing :
    ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] {I : Ideal A},
      TopologicalRing.Ideal.IsWeakIdealOfDefinition I → HenselianRing A I)

@[expose] public section
