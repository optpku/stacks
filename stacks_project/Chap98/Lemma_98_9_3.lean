/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Lifting
import StacksCheckRecall

/-!
# Lifting formal objects along morphisms formally smooth on objects
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

/- Lemma 98.9.3: a morphism of categories fibred in groupoids over a locally
Noetherian scheme that is formally smooth on objects lifts a formal object
from a specified residue-field lift, over the same Noetherian complete local
ring and structure morphism. The natural isomorphism is vertical at every
truncation. Lean stage zero is source stage one, the residue-field stage. -/
@[stacks 07X5]
#check (AlgebraicGeometry.GroupoidsOver.FormalObject.exists_lift :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (toS : Spec (CommRingCat.of R) ⟶ S)
    (hres : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS))
    (F : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects F]
    (η : ℕ ⥤ Y.total) (hη : η ⋙ Y.p = AdicPresentation.diagram toS (maximalIdeal R))
    (ξ1 : X.total) (hξ1 : X.p.obj ξ1 = (AdicPresentation.diagram toS (maximalIdeal R)).obj 0)
    (e : (FiberedCategoryOver.Groupoids.toFunctor F).obj ξ1 ≅ η.obj 0)
    (he : Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e.hom),
    ∃ ξ : ℕ ⥤ X.total, ξ ⋙ X.p = AdicPresentation.diagram toS (maximalIdeal R) ∧
      ∃ α : ξ ⋙ FiberedCategoryOver.Groupoids.toFunctor F ≅ η,
        ∀ n, Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj n))
          (α.hom.app n))

-- The lift can preserve the specified first-stage object and image isomorphism.
#check (AlgebraicGeometry.GroupoidsOver.FormalObject.exists_lift_stageOne :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (toS : Spec (CommRingCat.of R) ⟶ S)
    (hres : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS))
    (F : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects F]
    (η : ℕ ⥤ Y.total) (hη : η ⋙ Y.p = AdicPresentation.diagram toS (maximalIdeal R))
    (ξ1 : X.total) (hξ1 : X.p.obj ξ1 = (AdicPresentation.diagram toS (maximalIdeal R)).obj 0)
    (e : (FiberedCategoryOver.Groupoids.toFunctor F).obj ξ1 ≅ η.obj 0)
    (he : Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e.hom),
    ∃ ξ : ℕ ⥤ X.total, ξ ⋙ X.p = AdicPresentation.diagram toS (maximalIdeal R) ∧
      ∃ (e0 : ξ.obj 0 ≅ ξ1)
        (α : ξ ⋙ FiberedCategoryOver.Groupoids.toFunctor F ≅ η),
        X.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj 0)) e0.hom ∧
          (∀ n, Y.p.IsHomLift (𝟙 ((AdicPresentation.diagram toS (maximalIdeal R)).obj n))
            (α.hom.app n)) ∧
          α.hom.app 0 = (FiberedCategoryOver.Groupoids.toFunctor F).map e0.hom ≫ e.hom)
