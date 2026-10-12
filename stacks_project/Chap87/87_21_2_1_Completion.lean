/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion

@[expose] public section

universe u

/- The weak-ideal completion is the compatible-family inverse limit of the residue rings
of an algebra over the weak ideals of definition of its base ring. -/
#check (TopologicalRing.weakIdealCompletion :
  ∀ (A A' : Type u) [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A'], Type u)

#check (TopologicalRing.weakIdealCompletion.of :
  ∀ (A A' : Type u) [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A'],
    A' →+* TopologicalRing.weakIdealCompletion A A')
