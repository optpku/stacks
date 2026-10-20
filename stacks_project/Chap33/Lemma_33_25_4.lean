module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.25.4 (1): a scheme smooth over a field is geometrically regular over that field. -/
@[stacks 056T] #check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyRegular_of_smooth_over_field :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth f],
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular f)

/- Lemma 33.25.4 (2): a scheme smooth over a field is geometrically normal over that field. -/
@[stacks 056T] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal_of_smooth :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth X.hom],
      AlgebraicGeometry.SchemeOverField.geometricallyNormal X)

/- Lemma 33.25.4 (3): a scheme smooth over a field is geometrically reduced over that field. -/
@[stacks 056T] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_of_smooth :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth X.hom],
      AlgebraicGeometry.SchemeOverField.geometricallyReduced X)
