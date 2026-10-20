module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_21_1
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

public import ReasLib.RingTheory.Topology.LocalMorphismProperty

/-!
# Local properties of morphisms of countably indexed weakly admissible rings

A property of morphisms of countably indexed weakly admissible rings is local
when it is stable under étale weak-ideal completion squares, descends along
those squares when `A → A'` is faithfully flat, and is stable under finite
products of targets.
-/

@[expose] public section

universe u

open TopologicalRing

#check (TopologicalRing.IsLocalMorphismProperty :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop) → Prop)
