/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.ModuleCokernel
public import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Module quotients for closed-subscheme ideals

Both target maps below are the identity on sections. Their module structures come from the
actual subscheme inclusion; no equality of ideal carriers is used to construct data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Local bijectivity in the coefficient universe of this comparison, proved using the native
essentially small site criterion. -/
theorem quotientSiteWEqualsLocallyBijective (Z : TopCat.{u}) :
    (Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let J := Opens.grothendieckTopology Z
  let K := (equivSmallModel.{u} (TopologicalSpace.Opens Z)).inverse.inducedTopology J
  letI : ∀ V : SmallModel.{u} (TopologicalSpace.Opens Z), PreservesColimitsOfShape
      (K.Cover V)ᵒᵖ (CategoryTheory.forget AddCommGrpCat.{u}) := fun V ↦ by
    letI : FinallySmall.{u} (K.Cover V)ᵒᵖ := finallySmall_of_essentiallySmall _
    exact FinallySmall.preservesColimitsOfShape_of_isFiltered
      (K.Cover V)ᵒᵖ (CategoryTheory.forget AddCommGrpCat.{u})
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

attribute [local instance 2000] quotientSiteWEqualsLocallyBijective

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The same-site coefficient map fixed by the actual closed-subscheme inclusion. -/
abbrev quotientCoefficientMap :=
  RingedSpace.Hom.commRingSheafPushforwardMap I.subschemeι.toShHom

/-- The same-site scalar-restriction target used to define the ideal's kernel subobject. -/
abbrev sameSiteQuotientTarget : RingedSpace.Modules X.toRingedSpace :=
  (SheafOfModules.pushforward.{u}
    (ringedSiteStructureMap.{u, u, u} I.quotientCoefficientMap)).obj
    (SheafOfModules.unit (ringSheaf.{u, u, u} _
      ((TopCat.Sheaf.pushforward CommRingCat.{u} I.subschemeι.toShHom.hom.base).obj
        I.subscheme.sheaf)))

/-- The direct-image structure module of the actual closed subscheme. -/
abbrev directQuotientTarget : RingedSpace.Modules X.toRingedSpace :=
  (SheafOfModules.pushforward
    (RingedSpace.Hom.toRingCatSheafHom I.subschemeι.toShHom)).obj
      (SheafOfModules.unit I.subscheme.toRingedSpace.ringCatSheaf)

/-- The same-site structure-module map whose native kernel defines `I.toSubobject`. -/
abbrev sameSiteQuotientMap := KernelIdeal.map I.quotientCoefficientMap

/-- The structure-module map with direct-image target. -/
abbrev directQuotientMap := SheafOfModules.unitToPushforwardObjUnit
  (RingedSpace.Hom.toRingCatSheafHom I.subschemeι.toShHom)

/-- Identity on sections, from the same-site target to the direct-image target. -/
def sameSiteToDirectQuotient : I.sameSiteQuotientTarget ⟶ I.directQuotientTarget where
  val.app U := ModuleCat.homMk (𝟙 _) (fun r ↦ by ext x; rfl)
  val.naturality := by intros; ext x; rfl

/-- Identity on sections, in the reverse direction. -/
def directToSameSiteQuotient : I.directQuotientTarget ⟶ I.sameSiteQuotientTarget where
  val.app U := ModuleCat.homMk (𝟙 _) (fun r ↦ by ext x; rfl)
  val.naturality := by intros; ext x; rfl

/-- The two presentations of the target have explicit mutually inverse section maps. -/
def quotientTargetIso : I.sameSiteQuotientTarget ≅ I.directQuotientTarget where
  hom := I.sameSiteToDirectQuotient
  inv := I.directToSameSiteQuotient
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

@[simp]
theorem sameSiteToDirectQuotient_app (U) (x : I.sameSiteQuotientTarget.val.obj U) :
    I.sameSiteToDirectQuotient.val.app U x = x := rfl

@[simp]
theorem directToSameSiteQuotient_app (U) (x : I.directQuotientTarget.val.obj U) :
    I.directToSameSiteQuotient.val.app U x = x := rfl

/-- The explicit target comparison preserves the specified structure map. -/
@[reassoc (attr := simp)]
theorem sameSiteQuotientMap_comp_targetIso_hom :
    I.sameSiteQuotientMap ≫ I.quotientTargetIso.hom = I.directQuotientMap := by
  ext U x
  rfl

/-- The actual coefficient map is locally surjective, using affine sections of the closed
immersion rather than an admitted ringed-space bridge. -/
theorem quotientCoefficientMap_isLocallySurjective :
    Sheaf.IsLocallySurjective I.quotientCoefficientMap := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).2
  intro U t x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, ?_, hxV⟩
  exact I.subschemeι.app_surjective V hV _

/-- The direct structure-module map is an epimorphism, by local surjectivity after forgetting
to additive sheaves. -/
theorem directQuotientMap_epi : Epi I.directQuotientMap := by
  let F := SheafOfModules.toSheaf X.toRingedSpace.ringCatSheaf
  letI : Sheaf.IsLocallySurjective
      (F.map I.directQuotientMap) :=
    ⟨fun t ↦ I.quotientCoefficientMap_isLocallySurjective.imageSieve_mem t⟩
  letI : Epi (F.map I.directQuotientMap) := Sheaf.epi_of_isLocallySurjective _
  constructor
  intro Z g h w
  apply F.map_injective
  apply (cancel_epi (F.map I.directQuotientMap)).1
  simpa only [← F.map_comp] using congrArg F.map w

/-- The same-site map used to define the kernel is a genuine module epimorphism. -/
theorem sameSiteQuotientMap_epi : Epi I.sameSiteQuotientMap := by
  letI := I.directQuotientMap_epi
  have h : I.directQuotientMap ≫ I.quotientTargetIso.inv = I.sameSiteQuotientMap := by
    rw [← I.sameSiteQuotientMap_comp_targetIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← h]
  infer_instance

/-- The module cokernel of the ideal inclusion, with its same-site target. -/
def toSubobjectCokernelSameSiteIso :
    cokernel I.toSubobject.arrow ≅ I.sameSiteQuotientTarget := by
  letI := I.sameSiteQuotientMap_epi
  exact KernelIdeal.moduleCokernelIso I.quotientCoefficientMap

/-- The module cokernel of the ideal inclusion is the direct-image structure module. -/
def toSubobjectCokernelIso :
    cokernel I.toSubobject.arrow ≅ I.directQuotientTarget := by
  exact I.toSubobjectCokernelSameSiteIso ≪≫ I.quotientTargetIso

/-- The direct-image identification carries the cokernel projection to the actual quotient map. -/
@[reassoc (attr := simp)]
theorem π_comp_toSubobjectCokernelIso_hom :
    cokernel.π I.toSubobject.arrow ≫ I.toSubobjectCokernelIso.hom =
      I.directQuotientMap := by
  letI := I.sameSiteQuotientMap_epi
  simpa [toSubobjectCokernelIso, toSubobjectCokernelSameSiteIso] using
    congrArg (fun f ↦ f ≫ I.quotientTargetIso.hom)
      (KernelIdeal.π_comp_moduleCokernelIso_hom I.quotientCoefficientMap)

end AlgebraicGeometry.Scheme.IdealSheafData
