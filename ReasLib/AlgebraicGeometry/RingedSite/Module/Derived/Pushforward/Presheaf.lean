/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued cohomology presheaves and higher direct images

This leaf keeps the module structure throughout the comparison in Lemma 21.7.4.  The
underlying-additive statement is a view of this comparison, not its primary owner.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom.HigherDirectImage.Presheaf

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The degree-`i` module-valued cohomology presheaf pushed from `X` to `Y`. -/
@[stacks 072W "module-valued cohomology presheaf before sheafification"]
noncomputable abbrev cohomologyFunctor
    (f : Hom X Y) (i : ℕ)
    [UnivLE.{max uX vX, z}]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{z} X)] :
    RingedSite.ModuleCat.{z} X ⥤
      PresheafOfModules.{z} Y.structureSheaf.obj :=
  (SheafOfModules.forget.{z} X.structureSheaf).rightDerived i ⋙
    PresheafOfModules.pushforward f.structureSheafMap.hom

/-- The sheafification of the module-valued cohomology presheaf of `f`. -/
@[stacks 072W "sheafified module-valued cohomology presheaf"]
noncomputable abbrev sheafifiedCohomologyFunctor
    (f : Hom X Y) (i : ℕ)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{z} X)]
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    RingedSite.ModuleCat.{z} X ⥤ RingedSite.ModuleCat.{z} Y :=
  cohomologyFunctor f i ⋙
    PresheafOfModules.sheafification (𝟙 Y.structureSheaf.obj)

/-- The module-presheaf pushforward followed by module sheafification, before any derived
functor is taken. -/
@[stacks 072W "sheafified module pushforward functor"]
noncomputable abbrev sheafifiedPushforwardFunctor
    (f : Hom X Y)
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    PresheafOfModules.{z} X.structureSheaf.obj ⥤ RingedSite.ModuleCat.{z} Y :=
  PresheafOfModules.pushforward.{z} f.structureSheafMap.hom ⋙
    PresheafOfModules.sheafification.{z} (𝟙 Y.structureSheaf.obj)

/-- The underived pushforward followed by module sheafification. -/
@[stacks 072W "underived sheafified module pushforward"]
noncomputable abbrev underivedFunctor
    (f : Hom X Y)
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    RingedSite.ModuleCat.{z} X ⥤ RingedSite.ModuleCat.{z} Y :=
  SheafOfModules.forget.{z} X.structureSheaf ⋙ sheafifiedPushforwardFunctor f

/-- The degree-`i` derived-presheaf presentation used before identifying it with higher direct
image. -/
@[stacks 072W "derived presentation of the sheafified cohomology presheaf"]
noncomputable abbrev derivedFunctor
    (f : Hom X Y) (i : ℕ)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{z} X)]
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    RingedSite.ModuleCat.{z} X ⥤ RingedSite.ModuleCat.{z} Y :=
  (SheafOfModules.forget.{z} X.structureSheaf).rightDerived i ⋙
    sheafifiedPushforwardFunctor f

/-- The objectwise underived comparison from sheafifying a pushed presheaf to module pushforward.
The map uses the identity restriction comparison followed by the module-sheafification counit. -/
@[stacks 072W "underived module pushforward comparison component"]
noncomputable def underivedAppIso
    (f : Hom X Y) (M : RingedSite.ModuleCat.{z} X)
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    (underivedFunctor f).obj M ≅ f.modulePushforward.obj M :=
  (PresheafOfModules.sheafification (𝟙 Y.structureSheaf.obj)).mapIso
      ((PresheafOfModules.Restriction.idIso Y.structureSheaf.obj).app
        ((SheafOfModules.forget Y.structureSheaf).obj
          (f.modulePushforward.obj M))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.structureSheaf.obj)).counit).app (f.modulePushforward.obj M)

/-- Naturality of the explicit underived comparison component. -/
@[stacks 072W "naturality of the underived module pushforward comparison component"]
theorem underivedAppIso_naturality
    (f : Hom X Y) {M N : RingedSite.ModuleCat.{z} X} (a : M ⟶ N)
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    (underivedFunctor f).map a ≫ (underivedAppIso f N).hom =
      (underivedAppIso f M).hom ≫ f.modulePushforward.map a := sorry

/-- The natural underived comparison underlying the higher-direct-image comparison. -/
@[stacks 072W "underived module pushforward comparison"]
noncomputable def underivedIso
    (f : Hom X Y)
    [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    underivedFunctor f ≅ f.modulePushforward :=
  NatIso.ofComponents (fun (M : RingedSite.ModuleCat.{z} X) => underivedAppIso f M)
    (fun {_ _} a => underivedAppIso_naturality f a)

section Derived

variable (f : Hom X Y)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasInjectiveResolutions (RingedSite.ModuleCat.{z} X)]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Forgetting module structure to module presheaves is additive. -/
@[stacks 072W "additivity of the module-sheaf inclusion"]
noncomputable instance moduleForget_additive :
    (SheafOfModules.forget.{z} X.structureSheaf).Additive := sorry

/-- The sheafified pushforward composite is additive. -/
@[stacks 072W "additivity of the sheafified module pushforward composite"]
noncomputable instance sheafifiedPushforward_additive :
    (sheafifiedPushforwardFunctor f).Additive := sorry

/-- The sheafified pushforward composite preserves homology. -/
@[stacks 072W "homology preservation of the sheafified module pushforward composite"]
noncomputable instance sheafifiedPushforward_preservesHomology :
    (sheafifiedPushforwardFunctor f).PreservesHomology := sorry

/-- Exact postcomposition identifies the derived presentation with the right-derived composite. -/
@[stacks 072W "right-derived postcomposition comparison for modules"]
noncomputable def rightDerivedPostcompIso (i : ℕ) :
    derivedFunctor f i ≅
      (SheafOfModules.forget.{z} X.structureSheaf ⋙
        sheafifiedPushforwardFunctor f).rightDerived i :=
  (Functor.RightDerived.postcompIso
    (SheafOfModules.forget.{z} X.structureSheaf)
    (sheafifiedPushforwardFunctor f) i).symm

/-- Right derivation transports the underived comparison to higher direct images. -/
@[stacks 072W "derived module pushforward comparison"]
noncomputable def pushforwardDerivedIso (i : ℕ) :
    (SheafOfModules.forget.{z} X.structureSheaf ⋙
      sheafifiedPushforwardFunctor f).rightDerived i ≅
      RingedSite.Hom.higherDirectImageModuleFunctor f i :=
  CategoryTheory.NatIso.rightDerived (underivedIso f) i

/-- The derived-presheaf presentation computes the module higher direct-image functor. -/
@[stacks 072W "derived module higher direct-image presentation"]
noncomputable def derivedIso (i : ℕ) :
    derivedFunctor f i ≅ RingedSite.Hom.higherDirectImageModuleFunctor f i :=
  rightDerivedPostcompIso f i ≪≫ pushforwardDerivedIso f i

/-- Lemma 21.7.4 (072W): the sheafified module-valued cohomology presheaf is the module
higher direct image. -/
@[stacks 072W "sheafified module cohomology presheaf equals higher direct image"]
noncomputable def iso (i : ℕ) :
    sheafifiedCohomologyFunctor f i ≅
      RingedSite.Hom.higherDirectImageModuleFunctor f i :=
  derivedIso f i

/-- The coefficient-module component of the canonical 072W comparison. -/
@[stacks 072W "coefficient component of the module higher-direct-image comparison"]
noncomputable abbrev objIso (M : RingedSite.ModuleCat.{z} X) (i : ℕ) :
    (sheafifiedCohomologyFunctor f i).obj M ≅
      RingedSite.Hom.higherDirectImageModule f M i :=
  (iso f i).app M

/-- Naturality of the coefficient-module component of the 072W comparison. -/
@[reassoc, stacks 072W "coefficient naturality of the module higher-direct-image comparison"]
theorem objIso_hom_naturality
    {M N : RingedSite.ModuleCat.{z} X} (a : M ⟶ N) (i : ℕ) :
    (sheafifiedCohomologyFunctor f i).map a ≫ (objIso f N i).hom =
      (objIso f M i).hom ≫ RingedSite.Hom.higherDirectImageModuleMap f a i := sorry

end Derived

end RingedSite.Hom.HigherDirectImage.Presheaf
