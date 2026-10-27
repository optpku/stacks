/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationAbelian
public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian

/-! # Cartesian inverse images along simplicial augmentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram.{u, v, max u v} C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

section InverseImage

variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type (max u v)))]
variable [IsAugmentation.{u, v, max u v} C J K u0]

/-- Inverse image of a set-valued sheaf along a simplicial augmentation is cartesian. -/
instance inverseImage_isCartesian (G : Sheaf K.toGrothendieck (Type (max u v))) :
    IsCartesian C J ((IsAugmentation.inverseImage.{u, v, max u v} C J K u0).obj G) := sorry

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{max u v}]
variable [HasSheafify (topology C J) AddCommGrpCat.{max u v}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]

/-- Inverse image of an abelian sheaf along a simplicial augmentation is cartesian. -/
instance abelianInverseImage_isCartesian
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{max u v}) :
    Abelian.IsCartesian C J
      ((IsAugmentation.abelianInverseImage.{u, v, max u v} C J K u0).obj G) := sorry

/-- The unbounded derived inverse image along a simplicial augmentation is cartesian. -/
instance derivedInverseImage_isCartesian
    (dK : DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{max u v})) :
    Derived.IsCartesian C J
      ((IsAugmentation.derivedInverseImage.{u, v, max u v} C J K u0).obj dK) := sorry

end Abelian

end InverseImage

end CategoryTheory.SimplicialSites
