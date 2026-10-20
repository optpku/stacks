/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Family
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits RingedSite.Localization

universe ι u v w z

variable (S : RingedSite.{u, v, w}) (X : S)
variable (K L : FormalCoproduct.{ι} (Over X))

/- Remark 85.15.7 (Ringed variant over an object)
Apply family localization to the ringed slice over X. This is the iterated-slice
presentation of C/K, canonically equivalent to the family of slices over the
underlying component objects, not definitionally equal to that presentation. -/
@[stacks 0D9V] #check
  (RingedSite.Localization.AtSR.site (X := RingedSite.localization S X) :
    ∀ K : FormalCoproduct.{ι} (Over X), RingedSite.{max ι u v, max ι u v, w})

#check
  (RingedSite.Localization.AtSR.modulesEquiv (X := RingedSite.localization S X) K :
    SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) K) ≌
      ∀ index : K.I,
        SheafOfModules.{z} ((RingedSite.localization S X).structureSheaf.over (K.obj index)))

section AmbientTopos

variable [UnivLE.{max ι u v, w}]
variable [HasSheafify
  (SemiRepresentableFamily.overTopology (RingedSite.localization S X).siteTopology K) (Type w)]
variable [∀ presheaf : (SemiRepresentableFamily.OverSite K)ᵒᵖ ⥤ Type w,
  (SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension presheaf]
variable [(SemiRepresentableFamily.overTopology
  (RingedSite.localization S X).siteTopology K).HasSheafCompose (forget RingCat.{w})]
variable [(RingedSite.localization S X).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [(SemiRepresentableFamily.forget K).IsCocontinuous
  (AtSR.site (X := RingedSite.localization S X) K).siteTopology
  (RingedSite.localization S X).siteTopology]

#check
  (RingedSite.Localization.AtSR.toAmbient (X := RingedSite.localization S X) K :
    RingedSite.ToposHom (AtSR.site (X := RingedSite.localization S X) K)
      (RingedSite.localization S X))

end AmbientTopos

section FamilyTopos

variable (φ : K ⟶ L)
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify
  (SemiRepresentableFamily.overTopology (RingedSite.localization S X).siteTopology K) (Type w)]
variable [∀ presheaf : (SemiRepresentableFamily.OverSite K)ᵒᵖ ⥤ Type w,
  (SemiRepresentableFamily.overMap φ).op.HasPointwiseRightKanExtension presheaf]
variable [(SemiRepresentableFamily.overTopology
  (RingedSite.localization S X).siteTopology K).HasSheafCompose (forget RingCat.{w})]
variable [(SemiRepresentableFamily.overTopology
  (RingedSite.localization S X).siteTopology L).HasSheafCompose (forget RingCat.{w})]
variable [(SemiRepresentableFamily.overMap φ).IsCocontinuous
  (AtSR.site (X := RingedSite.localization S X) K).siteTopology
  (AtSR.site (X := RingedSite.localization S X) L).siteTopology]

#check
  (RingedSite.Localization.AtSR.map (X := RingedSite.localization S X) φ :
    RingedSite.ToposHom (AtSR.site (X := RingedSite.localization S X) K)
      (AtSR.site (X := RingedSite.localization S X) L))

end FamilyTopos

section AmbientExtension

variable [UnivLE.{max ι v, z}]
variable [HasWeakSheafify (RingedSite.localization S X).siteTopology AddCommGrpCat.{z}]
variable [(RingedSite.localization S X).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]

#check
  (RingedSite.Localization.AtSR.moduleLowerShriekAdjunction
      (X := RingedSite.localization S X) K :
    AtSR.moduleLowerShriek (X := RingedSite.localization S X) K ⊣
      RingedSite.Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K)
        (RingedSite.localization S X).structureSheaf)

#check
  (RingedSite.Localization.AtSR.moduleLowerShriek_exact
      (X := RingedSite.localization S X) K :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) K))
      (SheafOfModules.{z} (RingedSite.localization S X).structureSheaf)
      (AtSR.moduleLowerShriek (X := RingedSite.localization S X) K))

section Coproduct

variable [UnivLE.{v, z}]
variable (F : ∀ index : K.I,
  SheafOfModules.{z} ((RingedSite.localization S X).structureSheaf.over (K.obj index)))
variable [HasCoproduct fun index : K.I ↦
  (SheafOfModules.Localization.lowerShriekDirectSum
    (RingedSite.localization S X).structureSheaf (K.obj index)).obj (F index)]

#check
  (RingedSite.Localization.AtSR.moduleLowerShriekCoprod_isIso
      (X := RingedSite.localization S X) K F :
    IsIso (AtSR.moduleLowerShriekCoprod (X := RingedSite.localization S X) K F))

end Coproduct

end AmbientExtension

section FamilyExtension

variable (φ : K ⟶ L)
variable [UnivLE.{max ι v, z}]
variable [HasWeakSheafify
  (SemiRepresentableFamily.overTopology (RingedSite.localization S X).siteTopology L)
  AddCommGrpCat.{z}]
variable [(SemiRepresentableFamily.overTopology
  (RingedSite.localization S X).siteTopology L).WEqualsLocallyBijective AddCommGrpCat.{z}]

#check
  (RingedSite.Localization.AtSR.map_moduleLowerShriek_exact
      (X := RingedSite.localization S X) φ :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) K))
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) L))
      (AtSR.mapModuleLowerShriek (X := RingedSite.localization S X) φ))

#check
  (RingedSite.Localization.AtSR.mapModuleLowerShriek_adjunction
      (X := RingedSite.localization S X) φ :
    AtSR.mapModuleLowerShriek (X := RingedSite.localization S X) φ ⊣
      AtSR.mapModulePullback (X := RingedSite.localization S X) φ)

end FamilyExtension

#check
  (RingedSite.Localization.AtSR.toAmbient_modulePullback_exact
      (X := RingedSite.localization S X) K :
    exactFunctor
      (SheafOfModules.{z} (RingedSite.localization S X).structureSheaf)
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) K))
      (RingedSite.Cocontinuous.moduleInverseImage (SemiRepresentableFamily.forget K)
        (RingedSite.localization S X).structureSheaf))

variable (φ : K ⟶ L)

#check
  (RingedSite.Localization.AtSR.map_modulePullback_exact
      (X := RingedSite.localization S X) φ :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) L))
      (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) K))
      (AtSR.mapModulePullback (X := RingedSite.localization S X) φ))
