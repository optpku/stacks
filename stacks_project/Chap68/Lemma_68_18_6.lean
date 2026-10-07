module

public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Topology of a field-valued fibre of algebraic spaces

If a point of an algebraic space is represented by a quasi-compact monomorphism
from the spectrum of a field, the map on points from the corresponding fibre
product is a topological embedding onto the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Topology
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y)

/-- Lemma 68.18.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y ∈ |Y|` be the class of a field-valued point `p` represented
by a quasi-compact monomorphism `Spec(k) ⟶ Y`. Then
`Points.map (fieldFiberι f p) : |fieldFiber f p| ⟶ |X|` is a homeomorphism onto its
image with the induced topology. -/
@[stacks 0AC8]
theorem fieldFiberι_isEmbedding [QuasiCompact p.hom] [Mono p.hom] :
    Topology.IsEmbedding (Points.map (fieldFiberι f p)) :=
  sorry

/-- Lemma 68.18.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y ∈ |Y|` be the class of a field-valued point `p` represented
by a quasi-compact monomorphism `Spec(k) ⟶ Y`. Then the image of
`Points.map (fieldFiberι f p)` is the set-theoretic fibre
`Points.map f ⁻¹' {Points.mk p}`. -/
@[stacks 0AC8]
theorem fieldFiberι_range [QuasiCompact p.hom] [Mono p.hom] :
    Set.range (Points.map (fieldFiberι f p)) = Points.map f ⁻¹' {Points.mk p} :=
  sorry

/-- The image of the field-valued fibre in `|X|` is the set-theoretic fibre over `y`
whenever `y` is the class of `p`. -/
theorem fieldFiberι_range_mk [QuasiCompact p.hom] [Mono p.hom] {y : Points Y}
    (hy : Points.mk p = y) :
    Set.range (Points.map (fieldFiberι f p)) = Points.map f ⁻¹' {y} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
