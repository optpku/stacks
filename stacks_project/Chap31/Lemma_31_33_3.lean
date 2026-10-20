/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Flat

universe u

/- Lemma 31.33.3 (1): flatness over the center makes the canonical closed immersion of the
strict transform into the base change an isomorphism. -/
@[stacks 080F] #check
  (AlgebraicGeometry.strictTransform_subschemeι_isIso_of_flatAt_over_center :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S)
      [AlgebraicGeometry.IsBlowup b I] (f : X ⟶ S),
      (∀ x : X, f.base x ∈ I.support → AlgebraicGeometry.Scheme.Hom.flatAt f x) →
        CategoryTheory.IsIso
          (AlgebraicGeometry.strictTransformIdealSheafData b (I.comap b) f).subschemeι)

/- Lemma 31.33.3 (2): flatness of a quasicoherent module over the center makes the canonical
quotient map from its pullback to its strict transform an isomorphism. -/
@[stacks 080F] #check
  (AlgebraicGeometry.Scheme.Modules.strictTransformπ_isIso_of_flatOverAt_over_center :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S)
      [AlgebraicGeometry.IsBlowup b I] (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      (∀ x : X, f.base x ∈ I.support →
        AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f x) →
        CategoryTheory.IsIso (AlgebraicGeometry.strictTransformπ b (I.comap b) f ℱ))
