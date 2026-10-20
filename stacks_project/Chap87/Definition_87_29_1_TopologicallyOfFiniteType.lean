module

public import ReasLib.RingTheory.Topology.FiniteType

@[expose] public section

/- The promoted topological finite-type class is available from its shared owner. -/
#check (Algebra.TopologicallyOfFiniteType :
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A], Prop)
