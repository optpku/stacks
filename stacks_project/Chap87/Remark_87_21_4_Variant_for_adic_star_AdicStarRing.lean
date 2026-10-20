module

public import ReasLib.RingTheory.Topology.AdicStar

/-! # Adic-star rings -/

@[expose] public section

universe u

#check (TopologicalRing.IsAdicStarRing :
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R], Prop)
