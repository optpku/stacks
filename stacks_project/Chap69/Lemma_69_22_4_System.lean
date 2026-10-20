/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Quotient

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toQuotientCohomology :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
      (F : X.Modules)
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules]
      (p n : ℕ),
      AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.cohomologyOver
          (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
        AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientCohomology
          I f F p n)
