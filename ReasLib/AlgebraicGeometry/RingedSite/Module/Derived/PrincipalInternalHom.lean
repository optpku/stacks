module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.GlobalSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExtendedCech
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived
open SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Derived restriction of scalars from a principal localization of the structure sheaf. -/
abbrev principalRestrictionDerived (s : (unitModule J O).sections) :
    max J (principalLocalization s) ⥤ max J O :=
  (restrictionAlong (principalSubmonoid s).toLocalizationSheaf).mapDerivedCategory

/-- A principal localization of the structure sheaf, placed in degree zero as an ambient module. -/
abbrev principalDerivedModule (s : (unitModule J O).sections) : max J O :=
  (principalRestrictionDerived s).obj
    ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J (principalLocalization s)) 0).obj
      (unitModule J (principalLocalization s)))

namespace PrincipalInternalHom

/-- Derived coextension to a principal localization, computed degreewise on a K-injective model. -/
def coextension (s : (unitModule J O).sections) (K : max J O) :
    max J (principalLocalization s) :=
  (DerivedCategory.Q :
    CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ ⥤
      max J (principalLocalization s)).obj
    (((coextendAlong (principalSubmonoid s).toLocalizationSheaf).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (InternalHom.injectiveModel K))

/-- A local localized scalar acts on a product of local-Hom components by precomposition. -/
private def sourceAction (s : (unitModule J O).sections)
    (F I : CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ)
    (U : Cᵒᵖ) (scalar : (principalLocalization s).obj.obj U) (degree : ℤ)
    (components : ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U) :
    ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U :=
  fun index ↦
    (SheafOfModules.restrictScalars
      ((J.overPullback RingCat U.unop).map
        (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
      (SheafOfModules.sectionActionHom (principalLocalization s) (F.X index) U.unop scalar) ≫
        components index

/-- A local localized scalar acts on the same local-Hom product by postcomposition. -/
private def targetAction (s : (unitModule J O).sections)
    (F I : CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ)
    (U : Cᵒᵖ) (scalar : (principalLocalization s).obj.obj U) (degree : ℤ)
    (components : ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U) :
    ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U :=
  fun index ↦ components index ≫
    (SheafOfModules.restrictScalars
      ((J.overPullback RingCat U.unop).map
        (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
      (SheafOfModules.sectionActionHom (principalLocalization s)
        (I.X (index + degree)) U.unop scalar)

/-- Each component of the source scalar action is precomposition by scalar multiplication. -/
private theorem sourceAction_apply (s : (unitModule J O).sections)
    (F I : CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ)
    (U : Cᵒᵖ) (scalar : (principalLocalization s).obj.obj U) (degree : ℤ)
    (components : ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U) (index : ℤ) :
    sourceAction s F I U scalar degree components index =
      (SheafOfModules.restrictScalars
        ((J.overPullback RingCat U.unop).map
          (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
        (SheafOfModules.sectionActionHom (principalLocalization s) (F.X index) U.unop scalar) ≫
          components index := sorry

/-- Each component of the target scalar action is postcomposition by scalar multiplication. -/
private theorem targetAction_apply (s : (unitModule J O).sections)
    (F I : CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ)
    (U : Cᵒᵖ) (scalar : (principalLocalization s).obj.obj U) (degree : ℤ)
    (components : ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
      ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
        (I.X (index + degree))) U) (index : ℤ) :
    targetAction s F I U scalar degree components index = components index ≫
      (SheafOfModules.restrictScalars
        ((J.overPullback RingCat U.unop).map
          (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
        (SheafOfModules.sectionActionHom (principalLocalization s)
          (I.X (index + degree)) U.unop scalar) := sorry

/-- Derived internal Hom between localized objects agrees with ambient derived internal Hom
after restriction of scalars. -/
theorem restriction_isomorphic (s : (unitModule J O).sections)
    (L N : max J (principalLocalization s)) :
    IsIsomorphic
      (InternalHom.obj ((principalRestrictionDerived s).obj L)
        ((principalRestrictionDerived s).obj N))
      ((principalRestrictionDerived s).obj (InternalHom.obj L N)) := sorry

/-- The restricted local-Hom model computes ambient derived internal Hom, and its source and
target localized scalar actions agree in every local section and cochain degree. -/
theorem structures_agree (s : (unitModule J O).sections)
    (L N : max J (principalLocalization s)) :
    let F := (DerivedCategory.Q :
      CochainComplex (ringedSiteModuleCategory J (principalLocalization s)) ℤ ⥤
        max J (principalLocalization s)).objPreimage L
    let I := InternalHom.injectiveModel N
    let restriction :=
      (restrictionAlong (principalSubmonoid s).toLocalizationSheaf).mapHomologicalComplex
        (ComplexShape.up ℤ)
    IsIsomorphic
      (InternalHom.obj ((principalRestrictionDerived s).obj L)
        ((principalRestrictionDerived s).obj N))
      (InternalHom.objOfModels (restriction.obj F) (restriction.obj I)) ∧
    ∀ (U : Cᵒᵖ) (scalar : (principalLocalization s).obj.obj U) (degree : ℤ)
      (components : ∀ index : ℤ, SheafOfModules.RingedSite.InternalHom.LocalHom O
        ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj (F.X index))
        ((restrictionAlong (principalSubmonoid s).toLocalizationSheaf).obj
          (I.X (index + degree))) U),
      (fun index : ℤ ↦
        (SheafOfModules.restrictScalars
          ((J.overPullback RingCat U.unop).map
            (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
          (SheafOfModules.sectionActionHom (principalLocalization s)
            (F.X index) U.unop scalar) ≫ components index) =
      (fun index : ℤ ↦ components index ≫
        (SheafOfModules.restrictScalars
          ((J.overPullback RingCat U.unop).map
            (ringSheafMap (principalSubmonoid s).toLocalizationSheaf))).map
          (SheafOfModules.sectionActionHom (principalLocalization s)
            (I.X (index + degree)) U.unop scalar)) := sorry

/-- Restricted derived coextension computes ambient derived internal Hom from the localized
structure module. -/
theorem coextensionObject_isomorphic (s : (unitModule J O).sections) (K : max J O) :
    IsIsomorphic ((principalRestrictionDerived s).obj (coextension s K))
      (InternalHom.obj (principalDerivedModule s) K) := sorry

/-- Ambient derived internal Hom from a localized object is computed by localized derived
internal Hom into derived coextension, followed by restriction of scalars. -/
theorem coextension_isomorphic (s : (unitModule J O).sections)
    (K : max J O) (L : max J (principalLocalization s)) :
    IsIsomorphic (InternalHom.obj ((principalRestrictionDerived s).obj L) K)
      ((principalRestrictionDerived s).obj (InternalHom.obj L (coextension s K))) := sorry

/-- Derived internal Hom from a principal localization is idempotent. -/
theorem idempotent (s : (unitModule J O).sections) (K : max J O) :
    IsIsomorphic
      (InternalHom.obj (principalDerivedModule s)
        (InternalHom.obj (principalDerivedModule s) K))
      (InternalHom.obj (principalDerivedModule s) K) := sorry

/-- Iterated derived internal Hom from principal localizations is derived internal Hom from
localization at the product of the parameters. -/
theorem mul_isomorphic (f g : (unitModule J O).sections) (K : max J O) :
    IsIsomorphic
      (InternalHom.obj (principalDerivedModule f)
        (InternalHom.obj (principalDerivedModule g) K))
      (InternalHom.obj (principalDerivedModule (GlobalSections.mul g f)) K) := sorry

end PrincipalInternalHom

end RingedSite.Hom.ModuleDerived
