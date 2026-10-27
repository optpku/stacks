/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived pushforward comparison after forgetting module structure

This module owns the direct-image form of the underlying-additive comparison.  The compatibility
square is made explicit at homotopy level, while the derived comparison is obtained through the
right-derived universal property and exposed together with reusable isomorphism companions.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape Opposite

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe z uX vX uY vY w

namespace RingedSite.Hom.ModuleSections

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (f : RingedSite.Hom X Y)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]

/-- The additive sheaf pushforward induced by a ringed-site morphism. -/
@[stacks 0D6J "underlying additive pushforward"]
abbrev additivePushforward :
    Sheaf X.siteTopology AddCommGrpCat.{z} ⥤
      Sheaf Y.siteTopology AddCommGrpCat.{z} :=
  f.sheafPushforwardContinuous (A := AddCommGrpCat.{z})

/-- The homotopy-to-derived additive sheaf pushforward. -/
@[stacks 0D6J "underlying additive pushforward on homotopy categories"]
abbrev additivePushforwardToDerived :
    HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  Functor.Homotopy.toDerived (additivePushforward f)

/- The right-derived witness is a property of the source abelian category.  It is exposed as a
shared instance so callers with the usual Grothendieck hypothesis do not rebuild a local proof. -/
/-- The additive sheaf pushforward right-derived-functor witness. -/
@[stacks 0D6J "additive pushforward right-derived model"]
noncomputable instance additivePushforwardToDerived_isRightDerived
    [IsGrothendieckAbelian
      (Sheaf X.siteTopology AddCommGrpCat.{z})] :
    Functor.HasRightDerivedFunctor
      (additivePushforwardToDerived f)
      (HomotopyCategory.quasiIso
        (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ)) := sorry

variable [Functor.HasRightDerivedFunctor
  (additivePushforwardToDerived f)
  (HomotopyCategory.quasiIso
    (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))]

section

/-- The derived additive sheaf pushforward. -/
@[stacks 0D6J "underlying additive derived pushforward"]
noncomputable abbrev additivePushforwardDerived :
    DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  Functor.totalRightDerived
    (additivePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
        DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
    (HomotopyCategory.quasiIso
      (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))

/-- The homotopy-level source of the pushforward forgetful comparison. -/
@[stacks 0D6J "pushforward forgetful source"]
noncomputable abbrev pushforwardSource :
    HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  modulePushforwardToDerived.{z} f ⋙
    (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategory

/-- The homotopy-level target of the pushforward forgetful comparison. -/
@[stacks 0D6J "pushforward forgetful target"]
noncomputable abbrev pushforwardTarget :
    HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
    additivePushforwardToDerived f

/-- The derived source of the pushforward forgetful comparison. -/
@[stacks 0D6J "derived pushforward forgetful source"]
noncomputable abbrev pushforwardSourceDerived :
    ModuleDerived.{z} X ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  modulePushforwardDerived.{z} f ⋙
    (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategory

/-- The derived target of the pushforward forgetful comparison. -/
@[stacks 0D6J "derived pushforward forgetful target"]
noncomputable abbrev pushforwardTargetDerived :
    ModuleDerived.{z} X ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) :=
  (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory ⋙
    additivePushforwardDerived f

/-- The underived pushforward compatibility isomorphism. -/
@[stacks 0D6J "pushforward underived underlying bridge"]
noncomputable def pushforwardUnderlyingIso :
    f.modulePushforward.{z} ⋙ underlyingAbelianSheafFunctor.{z} Y ≅
      underlyingAbelianSheafFunctor.{z} X ⋙ additivePushforward f :=
  Iso.refl _

/-- The homotopy-level compatibility of module pushforward with forgetting scalars. -/
@[stacks 0D6J "pushforward homotopy underlying bridge"]
noncomputable def pushforwardHomotopyIso :
    (f.modulePushforward.{z}).mapHomotopyCategory (up ℤ) ⋙
        (underlyingAbelianSheafFunctor.{z} Y).mapHomotopyCategory (up ℤ) ≅
      (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
        (additivePushforward f).mapHomotopyCategory (up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (f.modulePushforward.{z} ⋙ underlyingAbelianSheafFunctor.{z} Y)) (up ℤ)) ≪≫
    Functor.mapHomotopyCategoryIso (pushforwardUnderlyingIso f) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (underlyingAbelianSheafFunctor.{z} X ⋙ additivePushforward f)) (up ℤ)).symm

/-- The homotopy-level compatibility transported through the derived localization. -/
@[stacks 0D6J "pushforward underlying bridge"]
noncomputable def pushforwardCompIso :
    pushforwardSource f ≅ pushforwardTarget f :=
  (Functor.associator
      ((f.modulePushforward.{z}).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} Y) (up ℤ) ⥤
          ModuleDerived.{z} Y)
      (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategory).symm ≪≫
    Functor.isoWhiskerLeft ((f.modulePushforward.{z}).mapHomotopyCategory (up ℤ))
      (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator
      ((f.modulePushforward.{z}).mapHomotopyCategory (up ℤ))
      ((underlyingAbelianSheafFunctor.{z} Y).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
          DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}))) ≪≫
    Functor.isoWhiskerRight (pushforwardHomotopyIso f)
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
          DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z})) ≪≫
    Functor.associator
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((additivePushforward f).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
          DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{z}))

/-- The homotopy-level pushforward bridge at one module complex. -/
@[stacks 0D6J "pushforward homotopy bridge component"]
noncomputable abbrev pushforwardHomotopyAppIso
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (pushforwardSource f).obj M ≅ (pushforwardTarget f).obj M :=
  (pushforwardCompIso f).app M

/-- The canonical right-derived unit for the pushforward source. -/
@[stacks 0D6J "pushforward forgetful source unit"]
noncomputable def pushforwardSourceUnit :
    pushforwardSource f ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X) ⋙ pushforwardSourceDerived f :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{z} f)
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
            ModuleDerived.{z} X)
        (ModuleQis.{z} X))
      (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategory ≫
    (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X)
      (modulePushforwardDerived.{z} f)
      (underlyingAbelianSheafFunctor.{z} Y).mapDerivedCategory).hom

/-- The canonical right-derived unit for the pushforward target. -/
@[stacks 0D6J "pushforward forgetful target unit"]
noncomputable def pushforwardTargetUnit :
    pushforwardTarget f ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X) ⋙ pushforwardTargetDerived f :=
  Functor.whiskerLeft
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (additivePushforwardToDerived f)
        (DerivedCategory.Qh :
          HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
            DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
        (HomotopyCategory.quasiIso
          (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))) ≫
    (Functor.associator
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
          DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
      (additivePushforwardDerived f)).inv ≫
    Functor.whiskerRight
      ((underlyingAbelianSheafFunctor.{z} X).mapDerivedCategoryFactorsh.inv :
        (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
            DerivedCategory.Qh ⟶
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
              ModuleDerived.{z} X) ⋙
            (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory)
      (additivePushforwardDerived f) ≫
    (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X)
      (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory
      (additivePushforwardDerived f)).hom

/-- The pushforward source is equipped with its right-derived-functor witness. -/
@[stacks 0D6J "pushforward underlying source model"]
noncomputable instance pushforwardSource_isRightDerived :
    (pushforwardSourceDerived f).IsRightDerivedFunctor
      (pushforwardSourceUnit f) (ModuleQis.{z} X) := sorry

/-- The pushforward target is equipped with its right-derived-functor witness. -/
@[stacks 0D6J "pushforward underlying target model"]
noncomputable instance pushforwardTarget_isRightDerived :
    (pushforwardTargetDerived f).IsRightDerivedFunctor
      (pushforwardTargetUnit f) (ModuleQis.{z} X) := sorry

/-- The derived pushforward underlying comparison as a reusable natural isomorphism. -/
@[stacks 0D6J "derived pushforward underlying comparison isomorphism"]
noncomputable def pushforwardIso :
    pushforwardSourceDerived f ≅ pushforwardTargetDerived f :=
  Functor.rightDerivedNatIso
    (pushforwardSourceDerived f) (pushforwardTargetDerived f)
    (pushforwardSourceUnit f) (pushforwardTargetUnit f)
    (ModuleQis.{z} X) (pushforwardCompIso f)

/-- The forward morphism of the derived pushforward underlying isomorphism. -/
@[stacks 0D6J "derived pushforward underlying comparison"]
noncomputable abbrev pushforwardComparison :
    pushforwardSourceDerived f ⟶ pushforwardTargetDerived f :=
  (pushforwardIso f).hom

/-- The pushforward comparison satisfies the right-derived universal-property equation. -/
@[stacks 0D6J "pushforward derived comparison factorization", reassoc (attr := simp)]
lemma pushforwardComparison_fac :
    pushforwardSourceUnit f ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (pushforwardComparison f) =
      (pushforwardCompIso f).hom ≫ pushforwardTargetUnit f := sorry

/-- The pushforward comparison factorization equation at a homotopy object. -/
@[stacks 0D6J "pushforward derived comparison factorization component"]
lemma pushforwardComparison_fac_app
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (pushforwardSourceUnit f).app M ≫
        (pushforwardComparison f).app
          ((DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (pushforwardCompIso f).hom.app M ≫
        (pushforwardTargetUnit f).app M := sorry

/-- The inverse pushforward comparison satisfies the reverse right-derived factorization equation. -/
@[stacks 0D6J "pushforward derived comparison reverse factorization", reassoc (attr := simp)]
lemma pushforwardComparison_inv_fac :
    pushforwardTargetUnit f ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (pushforwardIso f).inv =
      (pushforwardCompIso f).inv ≫ pushforwardSourceUnit f := sorry

/-- The reverse pushforward comparison factorization at a homotopy object. -/
@[stacks 0D6J "pushforward derived comparison reverse factorization component"]
lemma pushforwardComparison_inv_fac_app
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (pushforwardTargetUnit f).app M ≫
        (pushforwardIso f).inv.app
          ((DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (pushforwardCompIso f).inv.app M ≫
        (pushforwardSourceUnit f).app M := sorry

/-- The derived pushforward underlying comparison at a module complex. -/
@[stacks 0D6J "derived pushforward underlying comparison component"]
noncomputable abbrev pushforwardAppIso (K : ModuleDerived.{z} X) :
    (pushforwardSourceDerived f).obj K ≅ (pushforwardTargetDerived f).obj K :=
  (pushforwardIso f).app K

end

end RingedSite.Hom.ModuleSections
