module

public import ReasLib.Topology.Algebra.TensorProduct.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalRing

/- Situation 87.21.6: a local property P of morphisms of WAdm^count is stable
under base change when P(B → A) implies P(C → A ⊗̂_B C). This is well-defined
because A ⊗̂_B C remains in WAdm^count by Lemma 87.4.12. -/
@[stacks 0GBC] #check (TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop) → Prop)
