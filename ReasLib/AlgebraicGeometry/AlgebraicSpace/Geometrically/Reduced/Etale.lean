module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.List.TFAE

/-!
# Étale criteria for geometric reducedness

Geometric reducedness at a point of an algebraic space can be tested on some,
or equivalently every, étale scheme neighbourhood of that point.
An algebraic space is geometrically reduced if and only if some surjective
étale scheme chart is geometrically reduced, or equivalently every étale scheme
chart is geometrically reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Geometric reducedness at a point of an algebraic space over a field is
equivalent to geometric reducedness at the selected point of some étale scheme
neighbourhood, and to geometric reducedness at the selected point of every such
neighbourhood. -/
theorem etaleLocalRing_isGeometricallyReduced_tfae {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (of k))} (x : Points X) :
    List.TFAE
      [GeometricallyReducedAt X x,
        ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
            Points.mapOfOver a u = x ∧ SchemeOverField.geometricallyReducedAt U u,
        ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
            Points.mapOfOver a u = x → SchemeOverField.geometricallyReducedAt U u] :=
  sorry

/-- An algebraic space over a field is geometrically reduced at a point if and
only if some étale scheme neighbourhood is geometrically reduced at its selected
point. -/
theorem isGeometricallyReducedAt_iff_exists_etale {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (of k))} (x : Points X) :
    GeometricallyReducedAt X x ↔
      ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          Points.mapOfOver a u = x ∧ SchemeOverField.geometricallyReducedAt U u :=
  (etaleLocalRing_isGeometricallyReduced_tfae x).out 0 1

/-- An algebraic space over a field is geometrically reduced at a point if and
only if every étale scheme neighbourhood is geometrically reduced at its selected
point. -/
theorem isGeometricallyReducedAt_iff_forall_etale {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (of k))} (x : Points X) :
    GeometricallyReducedAt X x ↔
      ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          Points.mapOfOver a u = x → SchemeOverField.geometricallyReducedAt U u :=
  (etaleLocalRing_isGeometricallyReduced_tfae x).out 0 2

/-- Geometric reducedness of an algebraic space over a field is equivalent to
geometric reducedness of some surjective étale scheme chart, and to geometric
reducedness of the source of every étale morphism from a scheme. -/
theorem geometricallyReduced_etale_tfae {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (of k))) :
    List.TFAE
      [GeometricallyReduced X,
        ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
            AlgebraicSpace.Surjective a ∧ SchemeOverField.geometricallyReduced U,
        ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
            SchemeOverField.geometricallyReduced U] :=
  sorry

/-- An algebraic space over a field is geometrically reduced if and only if
some surjective étale morphism from a scheme has geometrically reduced source. -/
theorem geometricallyReduced_iff_exists_surjective_etale {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyReduced X ↔
      ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          AlgebraicSpace.Surjective a ∧ SchemeOverField.geometricallyReduced U :=
  (geometricallyReduced_etale_tfae X).out 0 1

/-- An algebraic space over a field is geometrically reduced if and only if
every étale morphism from a scheme has geometrically reduced source. -/
theorem geometricallyReduced_iff_forall_etale {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyReduced X ↔
      ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          SchemeOverField.geometricallyReduced U :=
  (geometricallyReduced_etale_tfae X).out 0 2

/-- Geometric reducedness at a point of an algebraic space over a field is
equivalent to geometric reducedness at its image under a morphism that is étale
at that point. -/
theorem geometricallyReducedAt_iff_of_etaleAt {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) {x : Points X}
    (hf : EtaleAt f x) :
    GeometricallyReducedAt X x ↔ GeometricallyReducedAt Y (Points.map f x) :=
  sorry

/-- The source of a surjective étale morphism of algebraic spaces over a field
is geometrically reduced if and only if its target is geometrically reduced. -/
theorem geometricallyReduced_iff_of_surjective_etale {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) [Etale f] [Surjective f] :
    GeometricallyReduced X ↔ GeometricallyReduced Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
