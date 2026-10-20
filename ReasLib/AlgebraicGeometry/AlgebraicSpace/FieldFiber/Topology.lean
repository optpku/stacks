module

public import Mathlib.Topology.Defs.Induced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Topology of a field-valued fibre of algebraic spaces

A field-valued point represented by a quasi-compact monomorphism has a fibre
whose canonical map on points is an embedding onto the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y)

/-- The canonical map on points from the fibre over a field-valued point represented
by a quasi-compact monomorphism is a topological embedding. -/
theorem fieldFiberι_isEmbedding [QuasiCompact p.hom] [Mono p.hom] :
    Topology.IsEmbedding (Points.map (fieldFiberι f p)) :=
  sorry

/-- The image on points of the fibre over a field-valued point represented by a
quasi-compact monomorphism is the preimage of the singleton represented by that point. -/
theorem fieldFiberι_range [QuasiCompact p.hom] [Mono p.hom] :
    Set.range (Points.map (fieldFiberι f p)) = Points.map f ⁻¹' {Points.mk p} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
