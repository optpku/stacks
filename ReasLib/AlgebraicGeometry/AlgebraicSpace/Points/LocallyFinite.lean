module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Inverse images under an algebraic-space morphism preserve locally finite families of
closed subsets of the canonical point spaces. -/
@[stacks 0EP6]
theorem locallyFinite_preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {I : Type v} (T : I → Closeds (Points Y))
    (hT : LocallyFinite (fun i ↦ (T i : Set (Points Y)))) :
    LocallyFinite
      (fun i ↦ ((T i).preimage (Points.continuous_map f) : Set (Points X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
