/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The morphism over `Spec A` induced by a ring homomorphism `A ⟶ B`. -/
def specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    ofOver (Over.mk (Spec.map φ)) ⟶ ofOver (Over.mk (𝟙 (Spec A))) :=
  ofOverHomMk (Spec.map φ) (Category.comp_id (Spec.map φ))

/-- The affine-spectrum morphism is the morphism induced by `Spec.map`. -/
theorem specMap_eq {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    specMap φ = ofOverHomMk (Spec.map φ) (Category.comp_id (Spec.map φ)) := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
