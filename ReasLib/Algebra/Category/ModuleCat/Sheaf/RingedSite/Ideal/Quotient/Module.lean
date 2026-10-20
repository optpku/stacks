module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules annihilated by an ideal sheaf

An ideal sheaf acts trivially on a module sheaf exactly when each section ideal acts trivially.
Such a module first descends to the sectionwise quotient presheaf, and module sheafification then
produces a module over the genuine quotient sheaf.  The underlying additive sheaf is compared
with the original module by the sheafification counit.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.IdealSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}}

/-- The ideal sheaf `I` annihilates the module sheaf `F` objectwise. -/
@[stacks 0H2K "ideal-sheaf annihilation"]
def IsAnnihilated
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) : Prop :=
  ∀ U : Cᵒᵖ, Module.IsTorsionBySet (O.obj.obj U) (F.val.obj U)
    (sections I U : Set (O.obj.obj U))

/-- Objectwise annihilation is equivalently containment of every section ideal in the
annihilator of the corresponding module of sections. -/
theorem isAnnihilated_iff
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) :
    IsAnnihilated I F ↔
      ∀ U : Cᵒᵖ, sections I U ≤
        Module.annihilator (O.obj.obj U) (F.val.obj U) := sorry

namespace Quotient

/-- The canonical action of `O(U) / I(U)` on `F(U)` when `I` annihilates `F`. -/
noncomputable abbrev sectionModule
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O)
    (h : IsAnnihilated I F) (U : Cᵒᵖ) :
    Module (sections I U) (F.val.obj U) :=
  (h U).module

/-- The quotient action on sections, exposed without changing the ambient instance environment. -/
noncomputable abbrev act
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O)
    (h : IsAnnihilated I F) (U : Cᵒᵖ)
    (r : sections I U) (m : F.val.obj U) : F.val.obj U :=
  (sectionModule I F h U).smul r m

/-- The quotient action is compatible with restriction maps. -/
theorem map_act
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    {U V : Cᵒᵖ} (f : U ⟶ V) (r : sections I U) (m : F.val.obj U) :
    F.val.map f (act I F h U r m) =
      act I F h V (restriction I f r) (F.val.map f m) := sorry

/-- Semilinearity of restriction, in the exact underlying-presheaf form used by the canonical
`PresheafOfModules.ofPresheaf` constructor. -/
theorem map_smul
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    {U V : Cᵒᵖ} (f : U ⟶ V) (r : (ringPresheaf (presheaf I)).obj U)
    (m : F.val.presheaf.obj U) :
    F.val.presheaf.map f ((sectionModule I F h U).smul r m) =
      (sectionModule I F h V).smul ((ringPresheaf (presheaf I)).map f r)
        (F.val.presheaf.map f m) := sorry

/-- The action of a class represented by `r` is the original action of `r`. -/
theorem act_projection
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    (U : Cᵒᵖ) (r : O.obj.obj U) (m : F.val.obj U) :
    act I F h U (sectionProjection I U r) m = r • m := sorry

/-- The quotient action is the unique action on the fixed additive group whose pullback along
`O(U) ⟶ O(U) / I(U)` is the original `O(U)`-action. -/
theorem act_unique
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O)
    (h : IsAnnihilated I F) (U : Cᵒᵖ)
    (N : Module (sections I U) (F.val.obj U))
    (hN : ∀ (r : O.obj.obj U) (m : F.val.obj U),
      N.smul (sectionProjection I U r) m = r • m)
    (q : sections I U) (m : F.val.obj U) :
    act I F h U q m = N.smul q m := sorry

/-- The quotient-module object on one object of the site. -/
noncomputable abbrev moduleObj
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O)
    (h : IsAnnihilated I F) (U : Cᵒᵖ) :
    ModuleCat.{z} ((ringPresheaf (presheaf I)).obj U) :=
  @ModuleCat.of (sections I U) _ (F.val.obj U) _ (sectionModule I F h U)

/-- Restriction as a linear map between the quotient-module objects. -/
noncomputable def moduleMap
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    moduleObj I F h U ⟶
      (ModuleCat.restrictScalars ((ringPresheaf (presheaf I)).map f).hom).obj
        (moduleObj I F h V) :=
  ConcreteCategory.ofHom (C := ModuleCat (sections I U))
    { toFun := ConcreteCategory.hom (F.val.map f)
      map_add' := fun x y ↦ map_add (ConcreteCategory.hom (F.val.map f)) x y
      map_smul' := map_smul I F h f }

/-- Identity restrictions act identically on quotient-module objects. -/
theorem moduleMap_id
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O)
    (h : IsAnnihilated I F) (U : Cᵒᵖ) :
    moduleMap I F h (𝟙 U) =
      (ModuleCat.restrictScalarsId' ((ringPresheaf (presheaf I)).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((ringPresheaf (presheaf I)).map_id U))).inv.app _ := sorry

/-- Composite restrictions act by the composite quotient-module map. -/
theorem moduleMap_comp
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    moduleMap I F h (f ≫ g) =
      moduleMap I F h f ≫
        (ModuleCat.restrictScalars ((ringPresheaf (presheaf I)).map f).hom).map
          (moduleMap I F h g) ≫
        (ModuleCat.restrictScalarsComp'
          ((ringPresheaf (presheaf I)).map f).hom
          ((ringPresheaf (presheaf I)).map g).hom
          ((ringPresheaf (presheaf I)).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringPresheaf (presheaf I)).map_comp f g))).inv.app _ := sorry

/-- The module presheaf over the sectionwise quotient presheaf whose underlying additive
presheaf is the underlying additive presheaf of `F`. -/
@[stacks 0H2K "quotient-module presheaf"]
noncomputable def modulePresheaf
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F) :
    PresheafOfModules.{z} (ringPresheaf (presheaf I)) where
  obj U := moduleObj I F h U
  map f := moduleMap I F h f
  map_id U := moduleMap_id I F h U
  map_comp f g := moduleMap_comp I F h f g

section Sheafification

variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Sheafification of the sectionwise quotient module presheaf, giving the canonical module
over the genuine quotient sheaf. -/
@[stacks 0H2K "quotient-module descent"]
noncomputable abbrev descend
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F) :
    ringedSiteModuleCategory.{u, v, z, w} J (sheaf I) :=
  (PresheafOfModules.moduleSheafification J (presheaf I)).obj
    (modulePresheaf I F h)

/-- The unit from the raw quotient-module presheaf to the underlying presheaf of its descended
module sheaf. -/
noncomputable abbrev descendUnit
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F) :
    modulePresheaf I F h ⟶
      (PresheafOfModules.moduleSheafificationRightAdjoint J (presheaf I)).obj
        (descend I F h) :=
  (PresheafOfModules.moduleSheafificationUnit J (presheaf I)).app
    (modulePresheaf I F h)

/-- The canonical image in the descended sheaf of an original local section. -/
noncomputable abbrev unitApp
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    (U : Cᵒᵖ) (m : F.val.obj U) : (descend I F h).val.obj U :=
  (descendUnit I F h).app U m

/-- The underlying additive sheaf of the descended quotient module is canonically the original
underlying additive sheaf. -/
noncomputable abbrev forgetIso
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F) :
    (SheafOfModules.toSheaf.{z}
      (SheafOfModules.RingedSite.ringSheaf J (sheaf I))).obj (descend I F h) ≅
      (SheafOfModules.toSheaf.{z}
        (SheafOfModules.RingedSite.ringSheaf J O)).obj F :=
  (PresheafOfModules.moduleSheafificationCompToSheaf J (presheaf I)).app
      (modulePresheaf I F h) ≪≫
    (CategoryTheory.sheafificationIso
      ((SheafOfModules.toSheaf.{z}
        (SheafOfModules.RingedSite.ringSheaf J O)).obj F)).symm

/-- Under the additive comparison, the sheafification unit sends an original section to itself. -/
theorem forgetIso_unit
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    (U : Cᵒᵖ) (m : F.val.obj U) :
    (forgetIso I F h).hom.hom.app U (unitApp I F h U m) = m := sorry

/-- Pulling the descended action back along `O ⟶ O / I` recovers the original action on the
canonical images of local sections. -/
theorem smul_projection
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory.{u, v, z, w} J O) (h : IsAnnihilated I F)
    (U : Cᵒᵖ) (r : O.obj.obj U) (m : F.val.obj U) :
    (forgetIso I F h).hom.hom.app U
        ((CategoryTheory.toSheafify J (presheaf I)).app U (sectionProjection I U r) •
          unitApp I F h U m) =
      r • m := sorry

end Sheafification

end Quotient

end SheafOfModules.RingedSite.IdealSheaf
