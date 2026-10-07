module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible

@[expose] public section

universe u

#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R], Ideal R → Prop)
