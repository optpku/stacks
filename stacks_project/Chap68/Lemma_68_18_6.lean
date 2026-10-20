module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Topology

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

/- Lemma 68.18.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y ∈ |Y|` be the class of a field-valued point `p` represented
by a quasi-compact monomorphism `Spec(k) ⟶ Y`. Then
`Points.map (fieldFiberι f p) : |fieldFiber f p| ⟶ |X|` is a homeomorphism onto its
image with the induced topology. -/
@[stacks 0AC8]
#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι_isEmbedding :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    [QuasiCompact p.hom] → [Mono p.hom] →
      Topology.IsEmbedding (Points.map (fieldFiberι f p)))

/- Lemma 68.18.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y ∈ |Y|` be the class of a field-valued point `p` represented
by a quasi-compact monomorphism `Spec(k) ⟶ Y`. Then the image of
`Points.map (fieldFiberι f p)` is the set-theoretic fibre
`Points.map f ⁻¹' {Points.mk p}`. -/
@[stacks 0AC8]
#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι_range :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y),
    [QuasiCompact p.hom] → [Mono p.hom] →
      Set.range (Points.map (fieldFiberι f p)) = Points.map f ⁻¹' {Points.mk p})

end AlgebraicGeometry.AlgebraicSpace
