/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u z

namespace CategoryTheory.Functor.AbelianPushforward

/-- A site whose object universe is bounded by the coefficient universe is locally small there. -/
private instance siteLocallySmall {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] : LocallySmall.{z} C :=
  ⟨fun U V ↦ @Small.trans_univLE.{u + 1, z, u} (U ⟶ V) inferInstance inferInstance⟩

/-- Comma categories over a small model of a site admit limits of additive groups. -/
private instance smallModelCommaLimits {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] (V : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (equivSmallModel.{z} C).inverse.op)
      AddCommGrpCat.{z} :=
  HasLimitsOfShape.of_small _ _

/-- Abelian sheaves on a site contained in the coefficient universe are Grothendieck abelian. -/
private instance sheafGrothendieck {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{z}] :
    IsGrothendieckAbelian.{z} (Sheaf J AddCommGrpCat.{z}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat.{z}

variable [UnivLE.{u + 1, z}]

variable {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
variable (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
variable (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
variable [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
variable [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasPointwiseRightKanExtension P]
variable [(f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive]
variable [(f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').Additive]

/-- Homotopy-to-derived presentation of cocontinuous abelian pushforward. -/
abbrev toDerived :
    HomotopyCategory (Sheaf J' AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Homotopy-to-derived presentation of continuous abelian inverse image. -/
abbrev inverseImageToDerived :
    HomotopyCategory (Sheaf K' AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf J' AddCommGrpCat.{z}) :=
  (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total right-derived functor of cocontinuous abelian
pushforward. -/
instance toDerived.hasRightDerived :
    Functor.HasRightDerivedFunctor (toDerived J' K' f)
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ)) :=
  Functor.RightDerived.KInjective.hasDerived
    (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K')

/-- Exact derived abelian inverse image is a left-derived functor of its
homotopy presentation. -/
instance inverseImageIsLeftDerived :
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f).IsLeftDerivedFunctor
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          J' K' f).obj.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- Existence of the total left-derived functor of continuous abelian inverse
image. -/
instance inverseImageToDerived.hasLeftDerived :
    Functor.HasLeftDerivedFunctor (inverseImageToDerived J' K' f)
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) :=
  Functor.HasLeftDerivedFunctor.mk'
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f)
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
      J' K' f).obj.mapDerivedCategoryFactorsh.hom

/-- The homotopy abelian inverse-image/pushforward adjunction descends to
derived categories. -/
instance derived.hasPair :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
        (up ℤ))
      (F := (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
        (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh (C := Sheaf K' AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh (C := Sheaf J' AddCommGrpCat.{z})) :=
  sorry

/-- Total right-derived abelian pushforward. -/
abbrev derived :
    DerivedCategory (Sheaf J' AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  Functor.totalRightDerived (toDerived J' K' f)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))

/-- The total-derived abelian inverse-image/pushforward adjunction. -/
def derived.totalAdjunction :
    Functor.totalLeftDerived (inverseImageToDerived J' K' f)
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) ⊣
      derived J' K' f :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K'))
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))

/-- The total left-derived abelian inverse image agrees with the exact derived
inverse image. -/
def inverseImageTotalDerivedIso :
    Functor.totalLeftDerived (inverseImageToDerived J' K' f)
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f :=
  Functor.leftDerivedNatIso
    (Functor.totalLeftDerived (inverseImageToDerived J' K' f)
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f)
    ((inverseImageToDerived J' K' f).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        J' K' f).obj.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

/-- Derived abelian inverse image is left adjoint to total right-derived
pushforward. -/
def derived.adjunction :
    siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f ⊣
      derived J' K' f :=
  (derived.totalAdjunction J' K' f).ofNatIsoLeft
    (inverseImageTotalDerivedIso J' K' f)

end CategoryTheory.Functor.AbelianPushforward
