module

import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Pushforward
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.33.4: for a blowup `b : S' ⟶ S`, an affine `S`-morphism `g : X ⟶ Y`,
and a quasicoherent module `ℱ` on `X`, pushforward along the base change of `g` carries the
strict transform of `ℱ` to an object isomorphic to the strict transform of its pushforward. -/
@[stacks 080G] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_strictTransformModule_isomorphic_of_isAffineHom :
    ∀ {S S' X Y : AlgebraicGeometry.Scheme.{u}}
      (I : S.IdealSheafData) (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b I]
      (g : X ⟶ Y) (y : Y ⟶ S) [AlgebraicGeometry.IsAffineHom g]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      CategoryTheory.IsIsomorphic
        (((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.strictTransformBaseChangeMap b g y)).obj
          (AlgebraicGeometry.strictTransformModule b (I.comap b) (g ≫ y) ℱ) :
            (AlgebraicGeometry.strictTransformAmbient b y).Modules))
        (AlgebraicGeometry.strictTransformModule b (I.comap b) y
          ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj ℱ)))
