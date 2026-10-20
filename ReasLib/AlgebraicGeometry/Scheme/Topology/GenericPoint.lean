module

public import ReasLib.Topology.Sober.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

/-!
# Component generic points and minimal specialization points of schemes
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace IsGenericPoint

/-- On a scheme, for a closed subset `T`, generic points of irreducible components of `T` are the
minimal specialization points of `T`. Closed subsets of schemes are sober, so these notions
match; the unrestricted statement is false. -/
theorem ofIrreducibleComponent_iff_mem_minimalSpecializationPoints
    {Y : Scheme.{u}} {T : Set Y} {y : Y} (hT : IsClosed T) :
    ofIrreducibleComponent y T ↔ y ∈ Y.minimalSpecializationPoints T :=
  sorry

end IsGenericPoint
