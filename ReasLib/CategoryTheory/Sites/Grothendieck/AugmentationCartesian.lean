/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos
public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.CategoryTheory.Sites.Topos.AbelianExact

/-! # Cartesian inverse images along fiberwise simplicial augmentations -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
include h_fiberwise
include h_aug


/-- Inverse image of a set-valued sheaf along a fiberwise augmentation is cartesian. -/
instance inverseImage_isCartesian (G : Sheaf K.toGrothendieck (Type w)) :
    Sheaf.IsCartesian F J (Type w) ((IsAugmentation.inverseImage F J K u0).obj G) := sorry

variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]

/-- Canonical abelian inverse image along a fiberwise augmentation is cartesian. -/
instance abelianInverseImage_isCartesian (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    Sheaf.IsCartesian F J AddCommGrpCat.{w}
      ((IsAugmentation.totalTopos F J K u0).abelianInverseImage.obj G) := sorry

variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- The unbounded derived abelian inverse image along the total fiberwise augmentation. -/
def IsAugmentation.derivedInverseImage :
    DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) :=
  (IsAugmentation.totalTopos F J K u0).abelianInverseImage.mapDerivedCategory

/-- Unbounded derived abelian inverse image along a fiberwise augmentation is cartesian. -/
instance derivedInverseImage_isCartesian
    (dK : DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian F J ((IsAugmentation.derivedInverseImage F J K u0).obj dK) := sorry

end CategoryTheory.Grothendieck
