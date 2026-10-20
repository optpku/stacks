module

public import ReasLib.RingTheory.Topology.LocalMorphismProperty
public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalRing

/- Situation 87.21.2: a property P of morphisms of WAdm^count is local when it
is stable under étale weak-ideal completion squares, descends along those
squares when A → A' is faithfully flat, and is stable under finite products of
targets. -/
@[stacks 0CBA] #check (TopologicalRing.IsLocalMorphismProperty :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop) → Prop)
