/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible

@[expose] public section

universe u

#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R], Ideal R → Prop)
