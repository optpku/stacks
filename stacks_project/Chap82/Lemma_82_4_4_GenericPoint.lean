module

public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

/-!
# Generic points of irreducible components of a subset

A point of a topological space is a generic point of an irreducible component of a subset `T`
when, as a point of the subspace `T`, it lies in `genericPoints T`. On a scheme, for a closed
subset this matches membership in `minimalSpecializationPoints`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace IsGenericPoint

/-- A point `x` is a generic point of an irreducible component of a subset `T`. -/
def ofIrreducibleComponent {X : Type u} [TopologicalSpace X] (x : X) (T : Set X) : Prop :=
  ∃ hx : x ∈ T, (⟨x, hx⟩ : T) ∈ genericPoints T

/-- Membership in `ofIrreducibleComponent` unpacks as subspace membership in `genericPoints`. -/
theorem ofIrreducibleComponent_iff {X : Type u} [TopologicalSpace X] (x : X) (T : Set X) :
    ofIrreducibleComponent x T ↔
      ∃ hx : x ∈ T, (⟨x, hx⟩ : T) ∈ genericPoints T :=
  sorry

/-- A generic point of an irreducible component of `T` lies in `T`. -/
theorem mem_ofIrreducibleComponent {X : Type u} [TopologicalSpace X] {x : X} {T : Set X}
    (h : ofIrreducibleComponent x T) : x ∈ T :=
  sorry

/-- On a scheme, for a closed subset `T`, generic points of irreducible components of `T` are the
minimal specialization points of `T`. Closed subsets of schemes are sober, so these notions
match; the unrestricted statement is false. -/
theorem ofIrreducibleComponent_iff_mem_minimalSpecializationPoints
    {Y : Scheme.{u}} {T : Set Y} {y : Y} (hT : IsClosed T) :
    ofIrreducibleComponent y T ↔ y ∈ Y.minimalSpecializationPoints T :=
  sorry

end IsGenericPoint
