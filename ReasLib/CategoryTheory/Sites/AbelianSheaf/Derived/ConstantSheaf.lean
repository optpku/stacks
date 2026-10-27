/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Comparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived.LowerShriek
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived lower shriek of constant abelian sheaves

The derived lower-shriek adjunction transposes the constant-sheaf restriction
comparison to a canonical morphism between degree-zero constant sheaves.
-/

@[expose] public section

noncomputable section

universe u z

namespace CategoryTheory.Functor.AbelianLowerShriek.derived

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
variable [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
variable [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P]

/-- The canonical morphism from derived abelian lower shriek of a degree-zero
constant sheaf to the degree-zero constant sheaf on the target site. -/
def constantSheafComparison (E : AddCommGrpCat.{z}) :
    (derived J K f).obj
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf J AddCommGrpCat.{z}).obj E)) ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf K AddCommGrpCat.{z}).obj E) :=
  ((derived.adjunction J K f).homEquiv
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf J AddCommGrpCat.{z}).obj E))
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf K AddCommGrpCat.{z}).obj E))).symm
    ((DerivedCategory.singleFunctor _ (0 : ℤ)).map
        (f.constantSheafRestrictionHom J K AddCommGrpCat.{z} E) ≫
      ((siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} J K f).obj.mapDerivedCategorySingleFunctor
          (0 : ℤ)).inv.app ((constantSheaf K AddCommGrpCat.{z}).obj E))

/-- Under the derived lower-shriek adjunction, the constant-sheaf comparison is
the degree-zero restriction comparison followed by exact inverse-image compatibility. -/
theorem constantSheafComparison_homEquiv (E : AddCommGrpCat.{z}) :
    (derived.adjunction J K f).homEquiv
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf J AddCommGrpCat.{z}).obj E))
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((constantSheaf K AddCommGrpCat.{z}).obj E))
        (constantSheafComparison J K f E) =
      (DerivedCategory.singleFunctor _ (0 : ℤ)).map
          (f.constantSheafRestrictionHom J K AddCommGrpCat.{z} E) ≫
        ((siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} J K f).obj.mapDerivedCategorySingleFunctor
            (0 : ℤ)).inv.app ((constantSheaf K AddCommGrpCat.{z}).obj E) :=
  Equiv.apply_symm_apply _ _

end CategoryTheory.Functor.AbelianLowerShriek.derived
