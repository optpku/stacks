/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Affine

/-!
# Ideal-power products from an affine ideal

The affine ideal-power owner supplies the inverse-image ideal, its product filtration,
and homogeneous multiplication maps.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.pullbackIdeal :
  ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))},
    Ideal A → (X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) →
      IdealSubobject X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.product :
  ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))},
    Ideal A → (X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) →
      (F : X.Modules) → ℕ → CategoryTheory.Subobject F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.actionMap :
  ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules) {m n : ℕ}, (I ^ m : Ideal A) →
      ((product I f F n : X.Modules) ⟶ (product I f F (m + n) : X.Modules)))
