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
