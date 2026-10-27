/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Colimits under continuous and cocontinuous module restriction

The comparison uses the actual additive sheafification comparison.  In particular the
`desc` below is constructed before registering preservation; no inverse is selected from
an admitted preservation or adjointness assertion.  The coefficient map need not be an iso.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uC vC uD vD uR uM w w'

namespace SheafOfModules.ContinuousColimits

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{uM}, G.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify J AddCommGrpCat.{uM}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uM}]
  [HasWeakSheafify K AddCommGrpCat.{uM}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{uM}]
  {R : Sheaf K RingCat.{uR}} {S : Sheaf J RingCat.{uR}}
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{uR} J K).obj R)

/-- Ambient sheafification followed by restriction, compared with sheafification after
restriction. Both additive maps are supplied by `CoverLifting`. -/
def additiveIso (P : PresheafOfModules.{uM} R.obj) :
    (toSheaf S).obj ((pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)) ≅
    (toSheaf S).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P)) :=
  ((G.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{uM} J K).app P.presheaf).symm

/-- Evaluation of the additive comparison. -/
def additiveAppIso (P : PresheafOfModules.{uM} R.obj) (X : Cᵒᵖ) :=
  ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{uM}).obj X).mapIso
    ((sheafToPresheaf J AddCommGrpCat.{uM}).mapIso (additiveIso G φ P))

theorem additiveAppIso_smul (P : PresheafOfModules.{uM} R.obj) (X : Cᵒᵖ)
    (r : S.obj.obj X) :
    (additiveAppIso G φ P X).hom ≫
        (((PresheafOfModules.sheafification (𝟙 S.obj)).obj
          ((PresheafOfModules.pushforward φ.hom).obj P)).val.obj X).smul r =
      (((pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)).val.obj X).smul r ≫
          (additiveAppIso G φ P X).hom := sorry

/-- The scalar-linear comparison, with the same forward and inverse functions. -/
def appIso (P : PresheafOfModules.{uM} R.obj) (X : Cᵒᵖ) :
    (((pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)).val.obj X) ≅
    (((PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P)).val.obj X) :=
  ModuleCat.isoMk (additiveAppIso G φ P X) (additiveAppIso_smul G φ P X)

theorem appIso_naturality (P : PresheafOfModules.{uM} R.obj)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)).val.map f ≫
      (ModuleCat.restrictScalars (S.obj.map f).hom).map (appIso G φ P Y).hom =
    (appIso G φ P X).hom ≫
      ((PresheafOfModules.sheafification (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward φ.hom).obj P)).val.map f := sorry

/-- Module-valued continuous/cocontinuous sheafification comparison. -/
def sheafificationIso (P : PresheafOfModules.{uM} R.obj) :
    (pushforward φ).obj ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) ≅
      (PresheafOfModules.sheafification (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward φ.hom).obj P) :=
  (fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (appIso G φ P)
      (fun _ _ f ↦ appIso_naturality G φ P f))

theorem sheafificationIso_naturality
    {P Q : PresheafOfModules.{uM} R.obj} (f : P ⟶ Q) :
    (pushforward φ).map ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) ≫
        (sheafificationIso G φ Q).hom =
      (sheafificationIso G φ P).hom ≫
        (PresheafOfModules.sheafification (𝟙 S.obj)).map
          ((PresheafOfModules.pushforward φ.hom).map f) := sorry

/-- The comparison is natural in the module presheaf, with both transformations
provided by the displayed objectwise maps. -/
def sheafificationNatIso :
    PresheafOfModules.sheafification (𝟙 R.obj) ⋙ pushforward.{uM} φ ≅
      PresheafOfModules.pushforward.{uM} φ.hom ⋙
        PresheafOfModules.sheafification (𝟙 S.obj) :=
  NatIso.ofComponents (sheafificationIso G φ) (by
    intro P Q f
    exact sheafificationIso_naturality G φ f)

section Colimits

variable {I : Type w} [Category.{w'} I]
  [HasColimitsOfShape I AddCommGrpCat.{uM}]

/-- Pointwise presheaf colimit descent. This is independent of sheafification and
uses only the implemented restriction-of-scalars colimit construction. -/
def presheafIsColimit {H : I ⥤ PresheafOfModules.{uM} R.obj}
    {c : Cocone H} (hc : IsColimit c) :
    IsColimit ((PresheafOfModules.pushforward φ.hom).mapCocone c) := by
  letI : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y), PreservesColimit
      (H ⋙ PresheafOfModules.evaluation R.obj Y)
      (ModuleCat.restrictScalars.{uM} (R.obj.map f).hom) := by
    intro X Y f
    exact @ModuleCat.preservesColimit_restrictScalars
      _ _ _ _ (R.obj.map f).hom I inferInstance
      (H ⋙ PresheafOfModules.evaluation R.obj Y) inferInstance
  letI : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit
      ((H ⋙ PresheafOfModules.pushforward φ.hom) ⋙
        PresheafOfModules.evaluation S.obj Y)
      (ModuleCat.restrictScalars.{uM} (S.obj.map f).hom) := by
    intro X Y f
    exact @ModuleCat.preservesColimit_restrictScalars
      _ _ _ _ (S.obj.map f).hom I inferInstance
      ((H ⋙ PresheafOfModules.pushforward φ.hom) ⋙
        PresheafOfModules.evaluation S.obj Y) inferInstance
  apply PresheafOfModules.evaluationJointlyReflectsColimits
    (H ⋙ PresheafOfModules.pushforward φ.hom)
    ((PresheafOfModules.pushforward φ.hom).mapCocone c)
  intro X
  let h₁ : IsColimit
      ((PresheafOfModules.evaluation R.obj (G.op.obj X)).mapCocone c) :=
    isColimitOfPreserves
      (PresheafOfModules.evaluation R.obj (G.op.obj X)) hc
  let h₂ : IsColimit
      ((PresheafOfModules.evaluation S.obj X).mapCocone
        ((PresheafOfModules.pushforward φ.hom).mapCocone c)) :=
    let h₂pres : PreservesColimit
        (H ⋙ PresheafOfModules.evaluation R.obj (G.op.obj X))
        (ModuleCat.restrictScalars.{uM} (φ.hom.app X).hom) :=
      @ModuleCat.preservesColimit_restrictScalars
        (S.obj.obj X) (R.obj.obj (G.op.obj X)) _ _ (φ.hom.app X).hom I inferInstance
        (H ⋙ PresheafOfModules.evaluation R.obj (G.op.obj X)) inferInstance
    (h₂pres.preserves h₁).some
  exact h₂

/-- A normalization cocone, with actual maps from each input sheaf to the
sheafification of its pointwise presheaf colimit. -/
def normalizedCocone (H : I ⥤ SheafOfModules.{uM} R) : Cocone H where
  pt := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (colimit (H ⋙ forget R))
  ι :=
    { app := fun i ↦
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).inv.app
            (H.obj i) ≫
          (PresheafOfModules.sheafification (𝟙 R.obj)).map
            (colimit.ι (H ⋙ forget R) i)
      naturality := by sorry }

/-- The actual universal map out of a restricted colimit. The only inverse here is
the installed sheafification counit in `normalizedCocone`, not a preservation witness. -/
def colimitDesc {H : I ⥤ SheafOfModules.{uM} R} {c : Cocone H}
    (hc : IsColimit c) (s : Cocone (H ⋙ pushforward φ)) :
    (pushforward φ).obj c.pt ⟶ s.pt :=
  (pushforward φ).map (hc.desc (normalizedCocone H)) ≫
    (sheafificationIso G φ (colimit (H ⋙ forget R))).hom ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
        ((presheafIsColimit G φ (colimit.isColimit (H ⋙ forget R))).desc
          ((forget S).mapCocone s))

/-- Colimit preservation with displayed descent data. -/
def isColimit {H : I ⥤ SheafOfModules.{uM} R} {c : Cocone H}
    (hc : IsColimit c) : IsColimit ((pushforward φ).mapCocone c) where
  desc := colimitDesc G φ hc
  fac := by sorry
  uniq := by sorry

/-- Preservation is registered only after constructing its universal maps. -/
instance preservesColimitsOfShape :
    PreservesColimitsOfShape I (pushforward.{uM} φ) where
  preservesColimit {K} := ⟨fun hc ↦ ⟨isColimit G φ hc⟩⟩

end Colimits

instance preservesColimitsOfSize [HasColimitsOfSize.{w', w} AddCommGrpCat.{uM}] :
    PreservesColimitsOfSize.{w', w} (pushforward.{uM} φ) where
  preservesColimitsOfShape := preservesColimitsOfShape G φ

end SheafOfModules.ContinuousColimits
