module

import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.33.2 (1): the canonical projection from the strict transform of `X` is the
blowup of `X` in the inverse-image center. -/
@[stacks 080E] #check
  (AlgebraicGeometry.strictTransformFst_isBlowup :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S)
      [AlgebraicGeometry.IsBlowup b I] (f : X ⟶ S),
      AlgebraicGeometry.IsBlowup
        (AlgebraicGeometry.strictTransformFst b (I.comap b) f) (I.comap f))

/- Lemma 31.33.2 (2): the strict transform of a quasicoherent module is canonically isomorphic
to the pushforward of its strict transform relative to the induced blowup of `X`. -/
@[stacks 080E] #check
  (AlgebraicGeometry.Scheme.Modules.strictTransformModule_isomorphic_pushforward_relativeStrictTransform :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S)
      [AlgebraicGeometry.IsBlowup b I] (f : X ⟶ S) (ℱ : X.Modules)
      [ℱ.IsQuasicoherent],
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.strictTransformModule b (I.comap b) f ℱ)
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.strictTransformRelativeMap b (I.comap b) f)).obj
          (AlgebraicGeometry.strictTransformModule
            (AlgebraicGeometry.strictTransformFst b (I.comap b) f)
            ((I.comap f).comap
              (AlgebraicGeometry.strictTransformFst b (I.comap b) f))
            (𝟙 X) ℱ)))
