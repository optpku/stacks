module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Regular.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 35.19.2: Let `f : X ⟶ Y` be a morphism of algebraic spaces. If `f` is
locally of finite presentation, flat, and surjective and `X` is regular, then `Y` is
regular. -/
@[stacks 06QN]
#check
  (AlgebraicGeometry.LocallyRingedSpace.Hom.regular_of_flat_of_surjective :
    ∀ {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f.toShHom],
      (∀ x : X, (f.stalkMap x).hom.EssFinitePresentation) →
      Function.Surjective f.base →
      (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
      ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
