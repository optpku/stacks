/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Exact

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u z

namespace CategoryTheory.Functor.AbelianLowerShriek

/-- Abelian sheaf pullback along a continuous functor of sites is additive. -/
instance constructionAdditive
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K]
    [HasWeakSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J K).Additive := sorry

/-- The homotopy-to-derived presentation of abelian lower shriek. -/
abbrev toDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [f.IsCocontinuous J K] [UnivLE.{u + 1, z}]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    HomotopyCategory (Sheaf J AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{z}) :=
  (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J K).mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total left-derived abelian lower-shriek functor. -/
instance toDerived.hasLeftDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [f.IsCocontinuous J K] [UnivLE.{u + 1, z}]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    Functor.HasLeftDerivedFunctor (toDerived J K f)
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- Total left-derived lower shriek of abelian sheaves. -/
abbrev derived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [f.IsCocontinuous J K] [UnivLE.{u + 1, z}]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    DerivedCategory (Sheaf J AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{z}) :=
  Functor.totalLeftDerived (toDerived J K f) DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{z}) (up ℤ))

/-- The homotopy inverse image of abelian sheaves has a total right-derived
functor. -/
instance inverseImageToDerived.hasRightDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    Functor.HasRightDerivedFunctor
      ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ)) :=
  Functor.RightDerived.Exact.hasFunctor (f.sheafPushforwardContinuous AddCommGrpCat.{z} J K)

/-- The homotopy abelian lower-shriek/inverse-image adjunction descends to
derived categories. -/
instance derived.hasPair
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J K).mapHomotopyCategory
        (up ℤ))
      (F := (f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh (C := Sheaf J AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh (C := Sheaf K AddCommGrpCat.{z})) := sorry

/-- The total-derived abelian lower-shriek/inverse-image adjunction. -/
def derived.totalAdjunction
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    derived J K f ⊣
      ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ)) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f AddCommGrpCat.{z} J K))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ))

/-- The total-right-derived abelian inverse image agrees with the exact derived
inverse image. -/
def inverseImageTotalDerivedIso
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ)) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J K f :=
  Functor.rightDerivedNatIso
    (((f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J K f)
    (((f.sheafPushforwardContinuous AddCommGrpCat.{z} J K).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} J K f).obj.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

/-- Derived abelian lower shriek is left adjoint to exact derived inverse image. -/
def derived.adjunction
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J : GrothendieckTopology C') (K : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J K] [UnivLE.{u + 1, z}] [f.IsCocontinuous J K]
    [HasSheafify J AddCommGrpCat.{z}] [HasSheafify K AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    derived J K f ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J K f :=
  (derived.totalAdjunction J K f).ofNatIsoRight
    (inverseImageTotalDerivedIso J K f)

end CategoryTheory.Functor.AbelianLowerShriek
