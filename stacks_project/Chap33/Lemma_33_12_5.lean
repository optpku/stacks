module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.12.5 (1): geometric regularity at a point descends along a morphism that is flat
at that point. -/
@[stacks 05AW] #check
  (AlgebraicGeometry.Scheme.Hom.geometricallyRegularAt_of_comp_of_flatAt :
    ∀ {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
      (x : X),
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt (f ≫ g) x →
        AlgebraicGeometry.Scheme.Hom.flatAt f x →
          AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt g (f x))

/- Lemma 33.12.5 (2): geometric regularity descends along a flat surjective morphism. -/
@[stacks 05AW] #check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyRegular_of_comp_of_flat_of_surjective :
    ∀ {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular (f ≫ g) →
        AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular g)
