/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Compatible

/-!
# Obstruction class of a map of mixed-scalar extensions on a first-order thickening

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, a pair of mixed-scalar extensions together
with maps of the endpoint 𝒪-modules whose infinitesimal-map square commutes determines a
canonical class in Ext ℱ ℒ 1, realized as the Ext¹ class of the 𝒪-module extension whose
middle term is the scalar extension along π of the middle homology of 𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Preadditive
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [hπ : IsFirstOrderThickening π]

/-- The infinitesimal-map square of φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ commutes. -/
def infMapCommSq (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) : Prop :=
  CommSq (infMap hπ.isSquareZero E) (moduleTensorMap (𝟙 (ideal π)) φ) ψ
    (infMap hπ.isSquareZero E')

/-- Commutativity of the infinitesimal-map square is equality of the two 𝒪-linear composites
ℐ ⊗ ℱ ⟶ ℒ. -/
theorem infMapCommSq_iff (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    infMapCommSq E E' φ ψ ↔
      infMap hπ.isSquareZero E ≫ ψ =
        moduleTensorMap (𝟙 (ideal π)) φ ≫ infMap hπ.isSquareZero E' := by
  exact ⟨fun h => h.w, fun h => ⟨h⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The composite of the signed inclusion and the sum of the quotient maps vanishes. -/
private theorem obsShortComplex_zero (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    biprod.lift E.ι (-((restrictionAlong π).map ψ ≫ E'.ι)) ≫
      biprod.desc (E.p ≫ (restrictionAlong π).map φ) E'.p = 0 := by
  simp only [biprod.lift_desc, neg_comp, Category.assoc, E'.zero, comp_zero,
    neg_zero, add_zero]
  rw [← Category.assoc, E.zero, zero_comp]

/-- The source complex 𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢 whose middle homology represents the obstruction. -/
noncomputable def obsShortComplex (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk (biprod.lift E.ι (-((restrictionAlong π).map ψ ≫ E'.ι)))
    (biprod.desc (E.p ≫ (restrictionAlong π).map φ) E'.p)
    (by exact obsShortComplex_zero E E' φ ψ)

/-- The two maps of `obsShortComplex` are `(1, -ψ)` and `(φ, 1)` on the middle biproduct. -/
theorem obsShortComplex_def (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (obsShortComplex E E' φ ψ).f =
        biprod.lift E.ι (-((restrictionAlong π).map ψ ≫ E'.ι)) ∧
      (obsShortComplex E E' φ ψ).g =
        biprod.desc (E.p ≫ (restrictionAlong π).map φ) E'.p := ⟨rfl, rfl⟩

/-- Middle homology of 𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢, as an 𝒪'-module. -/
noncomputable def obsHomology (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪' :=
  (obsShortComplex E E' φ ψ).homology

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of ℒ into the middle of `obsShortComplex` lands in the cycles. -/
private theorem obsι_comp_g (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (E'.ι ≫ biprod.inr) ≫ (obsShortComplex E E' φ ψ).g = 0 := by
  simp [obsShortComplex, Category.assoc, E'.zero]

/-- The 𝒪'-linear map ℒ ⟶ ℋ induced by inr : 𝒢' ⟶ ℱ' ⊞ 𝒢' through cycles. -/
noncomputable def obsι (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (restrictionAlong π).obj E'.kernel ⟶ obsHomology E E' φ ψ :=
  (obsShortComplex E E' φ ψ).liftCycles (E'.ι ≫ biprod.inr) (by exact obsι_comp_g E E' φ ψ) ≫
    (obsShortComplex E E' φ ψ).homologyπ

set_option backward.isDefEq.respectTransparency false in
/-- The composite of `toCycles` with the projection of cycles onto ℱ vanishes. -/
private theorem toCycles_comp_obsπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (obsShortComplex E E' φ ψ).toCycles ≫
      ((obsShortComplex E E' φ ψ).iCycles ≫ biprod.fst ≫ E.p) = 0 := by
  rw [ShortComplex.toCycles_i_assoc]
  simp [obsShortComplex, ← Category.assoc, E.zero]

/-- The 𝒪'-linear map ℋ ⟶ ℱ induced by fst : ℱ' ⊞ 𝒢' ⟶ ℱ' through homology. -/
noncomputable def obsπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    obsHomology E E' φ ψ ⟶ (restrictionAlong π).obj E.quot :=
  (obsShortComplex E E' φ ψ).descHomology
    ((obsShortComplex E E' φ ψ).iCycles ≫ biprod.fst ≫ E.p)
    (by exact toCycles_comp_obsπ E E' φ ψ)

/-- The middle homology is annihilated by the kernel ideal of π, using commutativity of the
infinitesimal-map square. -/
theorem obsHomology_isAnnihilated (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    IdealSheaf.IsAnnihilated (KernelIdeal.subobject π) (obsHomology E E' φ ψ) := sorry

variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]

/-- The 𝒪-module obtained by extending scalars of the middle homology along π. -/
noncomputable def obsModule (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪 :=
  (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
    (obsHomology E E' φ ψ)

/-- `obsModule` is extension of scalars of `obsHomology` along π. -/
theorem obsModule_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    obsModule E E' φ ψ =
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
        (obsHomology E E' φ ψ) := rfl

/-- The 𝒪-linear inclusion ℒ ⟶ ℋ corresponding to `obsι`. -/
noncomputable def obsModuleι (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    E'.kernel ⟶ obsModule E E' φ ψ :=
  (SheafOfModules.restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
      E'.kernel (obsModule E E' φ ψ)).symm
    (obsι E E' φ ψ ≫
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap π)).unit.app (obsHomology E E' φ ψ))

/-- The 𝒪-linear projection ℋ ⟶ ℱ corresponding to `obsπ`. -/
noncomputable def obsModuleπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    obsModule E E' φ ψ ⟶ E.quot :=
  (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
      (obsπ E E' φ ψ) ≫
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap π)).counit.app E.quot

set_option backward.isDefEq.respectTransparency false in
/-- The descended inclusion followed by the descended projection is zero. -/
private theorem obsExtension_zero (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    obsModuleι E E' φ ψ ≫ obsModuleπ E E' φ ψ = 0 := by
  let adj := SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)
  have hzero : obsι E E' φ ψ ≫ obsπ E E' φ ψ = 0 := by
    simp [obsι, obsπ, Category.assoc]
  have hι : (restrictionAlong π).map (obsModuleι E E' φ ψ) =
      obsι E E' φ ψ ≫ adj.unit.app (obsHomology E E' φ ψ) := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (ringSheafMap π).hom (obsModule E E' φ ψ).isSheaf).apply_symm_apply _
  have hp : adj.unit.app (obsHomology E E' φ ψ) ≫
      (restrictionAlong π).map (obsModuleπ E E' φ ψ) = obsπ E E' φ ψ :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.restrictScalars (ringSheafMap π).hom).map_injective
  change ((restrictionAlong π).map (obsModuleι E E' φ ψ ≫ obsModuleπ E E' φ ψ)).val =
    ((restrictionAlong π).map (0 : E'.kernel ⟶ E.quot)).val
  exact congrArg SheafOfModules.Hom.val (by
    rw [Functor.map_comp, hι, Category.assoc, hp, hzero, Functor.map_zero])

/-- The descended complex ℒ ⟶ ℋ ⟶ ℱ over the quotient ring sheaf. -/
noncomputable def obsExtension (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :=
  ShortComplex.mk (obsModuleι E E' φ ψ) (obsModuleπ E E' φ ψ)
    (by exact obsExtension_zero E E' φ ψ)

/-- The descended complex is short exact when the infinitesimal-map square commutes. -/
theorem obsExtension_shortExact (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    (obsExtension E E' φ ψ).ShortExact := sorry

/-- The descended sequence is short exact, with middle term the scalar extension of homology
and maps the descended inclusion and projection. -/
theorem obsExtension_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    (obsExtension E E' φ ψ).ShortExact ∧
      (obsExtension E E' φ ψ).X₂ = obsModule E E' φ ψ ∧
      (obsExtension E E' φ ψ).f = obsModuleι E E' φ ψ ∧
      (obsExtension E E' φ ψ).g = obsModuleπ E E' φ ψ :=
  ⟨obsExtension_shortExact E E' φ ψ h, rfl, rfl, rfl⟩

variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

namespace Extension

/-- The obstruction class o(φ, ψ) ∈ Ext¹_𝒪(ℱ, ℒ) of a pair of endpoint maps whose
infinitesimal-map square commutes. -/
noncomputable def mapObstruction (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    Ext E.quot E'.kernel 1 :=
  (obsExtension_shortExact E E' φ ψ h).extClass

/-- The obstruction is the Ext¹ class of the descended short exact complex. -/
theorem mapObstruction_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    mapObstruction E E' φ ψ h =
      (obsExtension_shortExact E E' φ ψ h).extClass := rfl

/-- The obstruction class of two endpoint maps vanishes if and only if there exists a
compatible map of the middle terms of their mixed-scalar extensions. -/
theorem mapObstruction_eq_zero_iff (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    mapObstruction E E' φ ψ h = 0 ↔ Nonempty (CompatibleMap E E' φ ψ) := sorry

end Extension

end SheafOfModules.RingedSite.FirstOrderThickening
