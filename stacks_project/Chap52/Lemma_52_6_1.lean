/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PrincipalInternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived
open SheafOfModules.RingedSite.ExtendedCech
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- Lemma 52.6.1 (1): for localized derived objects, ambient sheaf-valued derived
internal Hom agrees with localized derived internal Hom after restriction of scalars. -/
@[stacks 0996] #check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.restriction_isomorphic :
  ∀ (s : (unitModule J O).sections) (L N : max J (principalLocalization s)),
    IsIsomorphic
      (InternalHom.obj ((principalRestrictionDerived s).obj L)
        ((principalRestrictionDerived s).obj N))
      ((principalRestrictionDerived s).obj (InternalHom.obj L N)))

/- Lemma 52.6.1 (1) in particular: the ambient derived internal-Hom model of two
localized objects has identical source and target localized scalar actions. -/
@[stacks 0996]
#check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.structures_agree :
  ∀ (s : (unitModule J O).sections) (L N : max J (principalLocalization s)),
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
            (I.X (index + degree)) U.unop scalar)))

/- Lemma 52.6.1 (2): ambient derived internal Hom from a localized object is
localized derived internal Hom into coextension, restricted to the original structure sheaf. -/
@[stacks 0996]
#check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.coextension_isomorphic :
  ∀ (s : (unitModule J O).sections) (K : max J O) (L : max J (principalLocalization s)),
    IsIsomorphic (InternalHom.obj ((principalRestrictionDerived s).obj L) K)
      ((principalRestrictionDerived s).obj
        (InternalHom.obj L (PrincipalInternalHom.coextension s K))))

/- Restricted coextension is the ambient derived internal Hom from the principal
localization of the structure sheaf. -/
#check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.coextensionObject_isomorphic :
  ∀ (s : (unitModule J O).sections) (K : max J O),
    IsIsomorphic ((principalRestrictionDerived s).obj (PrincipalInternalHom.coextension s K))
      (InternalHom.obj (principalDerivedModule s) K))

/- Lemma 52.6.1 (2) in particular: derived internal Hom from the principal
localization is idempotent. -/
@[stacks 0996]
#check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.idempotent :
  ∀ (s : (unitModule J O).sections) (K : max J O),
    IsIsomorphic
      (InternalHom.obj (principalDerivedModule s)
        (InternalHom.obj (principalDerivedModule s) K))
      (InternalHom.obj (principalDerivedModule s) K))

/- Lemma 52.6.1 (3): iterated derived internal Hom with outer parameter f and inner
parameter g agrees with derived internal Hom from the localization at gf. -/
@[stacks 0996]
#check (RingedSite.Hom.ModuleDerived.PrincipalInternalHom.mul_isomorphic :
  ∀ (f g : (unitModule J O).sections) (K : max J O),
    IsIsomorphic
      (InternalHom.obj (principalDerivedModule f)
        (InternalHom.obj (principalDerivedModule g) K))
      (InternalHom.obj (principalDerivedModule (GlobalSections.mul g f)) K))
