/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.Remark_91_10_10_Thickening
public import stacks_project.Chap91.«91_10_0_1_Extension»

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
        moduleTensorMap (𝟙 (ideal π)) φ ≫ infMap hπ.isSquareZero E' := sorry

/-- An 𝒪'-linear map of middle terms of mixed-scalar extensions, compatible with given endpoint
maps φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ. -/
structure Compatible (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (φ' : E.middle ⟶ E'.middle) : Prop where
  /-- Compatibility with the inclusions of 𝒦 and ℒ. -/
  comm_ι : E.ι ≫ φ' = (restrictionAlong π).map ψ ≫ E'.ι
  /-- Compatibility with the projections onto ℱ and 𝒢. -/
  comm_p : φ' ≫ E'.p = E.p ≫ (restrictionAlong π).map φ

/-- Assemble compatibility of a middle map from the two commuting squares with ψ and φ. -/
def Compatible.ofComm {E E' : Extension π}
    {φ : E.quot ⟶ E'.quot} {ψ : E.kernel ⟶ E'.kernel}
    (φ' : E.middle ⟶ E'.middle)
    (hι : E.ι ≫ φ' = (restrictionAlong π).map ψ ≫ E'.ι)
    (hp : φ' ≫ E'.p = E.p ≫ (restrictionAlong π).map φ) :
    Compatible E E' φ ψ φ' where
  comm_ι := hι
  comm_p := hp

/-- A middle map is compatible with φ and ψ if and only if both endpoint squares commute. -/
theorem Compatible_iff {E E' : Extension π}
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (φ' : E.middle ⟶ E'.middle) :
    Compatible E E' φ ψ φ' ↔
      E.ι ≫ φ' = (restrictionAlong π).map ψ ≫ E'.ι ∧
        φ' ≫ E'.p = E.p ≫ (restrictionAlong π).map φ := sorry

/-- The source complex 𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢 whose middle homology represents the obstruction. -/
noncomputable def obsShortComplex (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk (biprod.lift E.ι (-((restrictionAlong π).map ψ ≫ E'.ι)))
    (biprod.desc (E.p ≫ (restrictionAlong π).map φ) E'.p) sorry

/-- The two maps of `obsShortComplex` are `(1, -ψ)` and `(φ, 1)` on the middle biproduct. -/
theorem obsShortComplex_def (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (obsShortComplex E E' φ ψ).f =
        biprod.lift E.ι (-((restrictionAlong π).map ψ ≫ E'.ι)) ∧
      (obsShortComplex E E' φ ψ).g =
        biprod.desc (E.p ≫ (restrictionAlong π).map φ) E'.p := sorry

/-- The composite of the two maps of `obsShortComplex` vanishes. -/
theorem obsShortComplex_zero (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (obsShortComplex E E' φ ψ).f ≫ (obsShortComplex E E' φ ψ).g = 0 := sorry

/-- Middle homology of 𝒦 ⟶ ℱ' ⊞ 𝒢' ⟶ 𝒢, as an 𝒪'-module. -/
noncomputable def obsHomology (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪' :=
  (obsShortComplex E E' φ ψ).homology

/-- The inclusion of ℒ into the middle of `obsShortComplex` lands in the cycles. -/
theorem obsι_comp_g (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (E'.ι ≫ biprod.inr) ≫ (obsShortComplex E E' φ ψ).g = 0 := sorry

/-- The 𝒪'-linear map ℒ ⟶ ℋ induced by inr : 𝒢' ⟶ ℱ' ⊞ 𝒢' through cycles. -/
noncomputable def obsι (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (restrictionAlong π).obj E'.kernel ⟶ obsHomology E E' φ ψ :=
  (obsShortComplex E E' φ ψ).liftCycles (E'.ι ≫ biprod.inr) (obsι_comp_g E E' φ ψ) ≫
    (obsShortComplex E E' φ ψ).homologyπ

/-- The composite of `toCycles` with the projection of cycles onto ℱ vanishes. -/
theorem toCycles_comp_obsπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    (obsShortComplex E E' φ ψ).toCycles ≫
      ((obsShortComplex E E' φ ψ).iCycles ≫ biprod.fst ≫ E.p) = 0 := sorry

/-- The 𝒪'-linear map ℋ ⟶ ℱ induced by fst : ℱ' ⊞ 𝒢' ⟶ ℱ' through homology. -/
noncomputable def obsπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel) :
    obsHomology E E' φ ψ ⟶ (restrictionAlong π).obj E.quot :=
  (obsShortComplex E E' φ ψ).descHomology
    ((obsShortComplex E E' φ ψ).iCycles ≫ biprod.fst ≫ E.p)
    (toCycles_comp_obsπ E E' φ ψ)

/-- The middle homology is annihilated by the kernel ideal of π, using commutativity of the
infinitesimal-map square. -/
theorem obsHomology_isAnnihilated (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    IdealSheaf.IsAnnihilated (KernelIdeal.subobject π) (obsHomology E E' φ ψ) := sorry

variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]

/-- The 𝒪-module obtained by extending scalars of the middle homology along π. -/
noncomputable def obsModule (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪 :=
  have := h
  (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
    (obsHomology E E' φ ψ)

/-- `obsModule` is extension of scalars of `obsHomology` along π. -/
theorem obsModule_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    obsModule E E' φ ψ h =
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
        (obsHomology E E' φ ψ) := sorry

/-- The 𝒪-linear inclusion ℒ ⟶ ℋ corresponding to `obsι`. -/
noncomputable def obsModuleι (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    E'.kernel ⟶ obsModule E E' φ ψ h :=
  (SheafOfModules.restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
      E'.kernel (obsModule E E' φ ψ h)).symm
    (obsι E E' φ ψ ≫
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap π)).unit.app (obsHomology E E' φ ψ))

/-- The 𝒪-linear projection ℋ ⟶ ℱ corresponding to `obsπ`. -/
noncomputable def obsModuleπ (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    obsModule E E' φ ψ h ⟶ E.quot :=
  (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
      (obsπ E E' φ ψ) ≫
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap π)).counit.app E.quot

/-- The descended 𝒪-module extension 0 ⟶ ℒ ⟶ ℋ ⟶ ℱ ⟶ 0 representing o(φ, ψ). -/
noncomputable def obsExtension (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    CategoryTheory.Extension E'.kernel E.quot where
  E := obsModule E E' φ ψ h
  f := obsModuleι E E' φ ψ h
  g := obsModuleπ E E' φ ψ h
  zero := sorry
  shortExact := sorry

/-- `obsExtension` is the short exact sequence 0 ⟶ ℒ ⟶ ℋ ⟶ ℱ ⟶ 0 in Mod 𝒪 with middle
`obsModule` and maps `obsModuleι`, `obsModuleπ`. -/
theorem obsExtension_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    (obsExtension E E' φ ψ h).toShortComplex.ShortExact ∧
      (obsExtension E E' φ ψ h).E = obsModule E E' φ ψ h ∧
      (obsExtension E E' φ ψ h).f = obsModuleι E E' φ ψ h ∧
      (obsExtension E E' φ ψ h).g = obsModuleπ E E' φ ψ h := sorry

variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The obstruction class o(φ, ψ) ∈ Ext¹_𝒪(ℱ, ℒ) of a pair of endpoint maps whose
infinitesimal-map square commutes. -/
noncomputable def mapObstruction (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    Ext E.quot E'.kernel 1 :=
  have := h
  (obsExtension E E' φ ψ h).extClass

/-- `mapObstruction` is the Ext¹ class of `obsExtension`. -/
theorem mapObstruction_spec (E E' : Extension π)
    (φ : E.quot ⟶ E'.quot) (ψ : E.kernel ⟶ E'.kernel)
    (h : infMapCommSq E E' φ ψ) :
    mapObstruction E E' φ ψ h = (obsExtension E E' φ ψ h).extClass := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
