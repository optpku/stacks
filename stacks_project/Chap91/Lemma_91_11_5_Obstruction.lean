/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap91.Lemma_91_11_1_IdealMul
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction class of a module map on a first-order thickening

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, an 𝒪-linear map φ : i^* ℱ' ⟶ i^* 𝒢'
determines a connecting class in Ext⁽1⁾(Li^* ℱ', ℐ 𝒢'). The class is the derived-adjunction
mate of the unit-sequence connecting map applied to the 𝒪'-adjoint of φ.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open DerivedCategory
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped DerivedExt

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [UnivLE.{max u v, max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{max u v} (sameSiteHom π))
  (ModuleQis.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))]
variable [DerivedAdjunction.HasPair.{max u v} (sameSiteHom π)]
variable [(modulePushforwardDerived (sameSiteHom π)).CommShift ℤ]

/-- Comparison `i_* M[0] ⟶ Ri_* (M[0])` from the underived degree-zero single to derived
direct image along the same-site thickening. -/
noncomputable def pushforwardSingleUnit
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).obj
        ((restrictionAlong π).obj M) ⟶
      (modulePushforwardDerived (sameSiteHom π)).obj
        ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
          (0 : ℤ)).obj M) :=
  Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (sameSiteHom π).modulePushforward (up ℤ) (0 : ℤ)).inv.app M) ≫
    ((modulePushforwardToDerived.{max u v} (sameSiteHom π)).totalRightDerivedUnit
      (moduleLocalization.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))
      (ModuleQis.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))).app
      ((HomotopyCategory.singleFunctor
        (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) (0 : ℤ)).obj M)

/-- `pushforwardSingleUnit` is the derived-category image of the single-complex comparison,
followed by the total right-derived unit of `i_*`. -/
theorem pushforwardSingleUnit_spec
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    pushforwardSingleUnit π M =
      Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (sameSiteHom π).modulePushforward (up ℤ) (0 : ℤ)).inv.app M) ≫
        ((modulePushforwardToDerived.{max u v} (sameSiteHom π)).totalRightDerivedUnit
          (moduleLocalization.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))
          (ModuleQis.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))).app
          ((HomotopyCategory.singleFunctor
            (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) (0 : ℤ)).obj M) :=
  sorry

/-- Connecting morphism of the unit sequence `0 ⟶ ℐ 𝒢' ⟶ 𝒢' ⟶ i_* i^* 𝒢' ⟶ 0`. -/
noncomputable def unitConnecting
    (G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).obj
        ((restrictionAlong π).obj
          ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')) ⟶
      ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).obj
          (idealMulO' π G'))⟦(1 : ℤ)⟧ :=
  (unitShortComplex_shortExact π G').singleδ

/-- `unitConnecting` is `singleδ` of the short exact unit sequence of 𝒢'. -/
theorem unitConnecting_spec
    (G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    unitConnecting π G' = (unitShortComplex_shortExact π G').singleδ := sorry

variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
variable (φ : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')

/-- The 𝒪'-adjoint of φ, as the composite of the unit of ℱ' with i_* φ. -/
def adjointHom :
    F' ⟶ (restrictionAlong π).obj
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G') :=
  extendRestrictUnit π F' ≫ (restrictionAlong π).map φ

/-- `adjointHom` is the unit of ℱ' followed by restriction of scalars of φ. -/
theorem adjointHom_spec :
    adjointHom π F' G' φ =
      extendRestrictUnit π F' ≫ (restrictionAlong π).map φ := sorry

/-- The connecting class of φ in Ext⁽1⁾_{𝒪'}(ℱ', ℐ 𝒢'). -/
noncomputable def obstructionO' :
    Ext⁽(1 : ℤ)⁾(
      (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).obj F',
      (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).obj
        (idealMulO' π G')) :=
  (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).map
      (adjointHom π F' G' φ) ≫
    unitConnecting π G'

/-- `obstructionO'` is the image of `adjointHom` under `singleδ` of the unit sequence. -/
theorem obstructionO'_spec :
    obstructionO' π F' G' φ =
      (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') (0 : ℤ)).map
          (adjointHom π F' G' φ) ≫
        unitConnecting π G' := sorry

/-- The canonical obstruction class o(φ) in Ext⁽1⁾_𝒪(Li^* ℱ', ℐ 𝒢'). -/
noncomputable def liftObstruction :
    Ext⁽(1 : ℤ)⁾(
      (SameSite.pullbackDerived π).obj
        ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
          (0 : ℤ)).obj F'),
      (singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
        (0 : ℤ)).obj (idealMul π G')) :=
  ((moduleDerivedAdjunction (sameSiteHom π)).homEquiv
      ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
        (0 : ℤ)).obj F')
      (((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
          (0 : ℤ)).obj (idealMul π G'))⟦(1 : ℤ)⟧)).symm
    (obstructionO' π F' G' φ ≫
      (shiftFunctor _ (1 : ℤ)).map
        ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
            (0 : ℤ)).map (extendRestrictUnit π (idealMulO' π G')) ≫
          pushforwardSingleUnit π (idealMul π G')) ≫
      ((modulePushforwardDerived (sameSiteHom π)).commShiftIso (1 : ℤ)).inv.app
        ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
          (0 : ℤ)).obj (idealMul π G')))

/-- `liftObstruction` is the derived-adjunction mate of `obstructionO'` postcomposed with
the unit of ℐ 𝒢' and the underived-to-derived pushforward comparison. -/
theorem liftObstruction_spec :
    ((moduleDerivedAdjunction (sameSiteHom π)).homEquiv
        ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
          (0 : ℤ)).obj F')
        (((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
            (0 : ℤ)).obj (idealMul π G'))⟦(1 : ℤ)⟧))
      (liftObstruction π F' G' φ) =
      obstructionO' π F' G' φ ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
              (0 : ℤ)).map (extendRestrictUnit π (idealMulO' π G')) ≫
            pushforwardSingleUnit π (idealMul π G')) ≫
        ((modulePushforwardDerived (sameSiteHom π)).commShiftIso (1 : ℤ)).inv.app
          ((singleFunctor (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
            (0 : ℤ)).obj (idealMul π G')) := sorry

/-- Vanishing of the 𝒪'-connecting class is equivalent to vanishing of `liftObstruction`. -/
theorem obstructionO'_eq_zero_iff_liftObstruction :
    obstructionO' π F' G' φ = 0 ↔ liftObstruction π F' G' φ = 0 := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
