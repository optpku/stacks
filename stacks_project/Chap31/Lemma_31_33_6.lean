/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.33.6 (1): for two successive blowups whose composite center has the prescribed
support, the direct strict transform of a quasicoherent module is isomorphic to the transported
iterated strict transform. -/
@[stacks 080I] #check
  (AlgebraicGeometry.Scheme.Modules.strictTransformModule_isomorphic_pushforward_iteratedStrictTransform :
    ∀ {S S' S'' X : AlgebraicGeometry.Scheme.{u}} (Z : S.IdealSheafData)
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b Z]
      (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [AlgebraicGeometry.IsBlowup b' Z']
      (Y : S.IdealSheafData),
      (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S') →
      ∀ [AlgebraicGeometry.IsBlowup (b' ≫ b) Y]
        (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        CategoryTheory.IsIsomorphic
          (AlgebraicGeometry.strictTransformModule (b' ≫ b) (Y.comap (b' ≫ b)) f ℱ)
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (CategoryTheory.Limits.pullbackLeftPullbackSndIso f b b').hom).obj
            (AlgebraicGeometry.strictTransformModule b' (Z'.comap b')
              (CategoryTheory.Limits.pullback.snd f b)
              (AlgebraicGeometry.strictTransformModule b (Z.comap b) f ℱ))))

/- Lemma 31.33.6 (2): under the same hypotheses, the direct strict transform of a scheme is
isomorphic to its iterated strict transform formed using the canonical structure morphism of
the first strict transform. -/
@[stacks 080I] #check
  (AlgebraicGeometry.strictTransform_isomorphic_iteratedStrictTransform :
    ∀ {S S' S'' X : AlgebraicGeometry.Scheme.{u}} (Z : S.IdealSheafData)
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b Z]
      (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [AlgebraicGeometry.IsBlowup b' Z']
      (Y : S.IdealSheafData),
      (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S') →
      ∀ [AlgebraicGeometry.IsBlowup (b' ≫ b) Y] (f : X ⟶ S),
        CategoryTheory.IsIsomorphic
          (AlgebraicGeometry.strictTransform (b' ≫ b) (Y.comap (b' ≫ b)) f)
          (AlgebraicGeometry.strictTransform b' (Z'.comap b')
            (AlgebraicGeometry.strictTransformSnd b (Z.comap b) f)))
