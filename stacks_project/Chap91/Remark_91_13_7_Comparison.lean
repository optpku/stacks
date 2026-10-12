/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_13_4
public import stacks_project.Chap91.Lemma_91_13_6_Map
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

/-!
# Ext¹ comparison for identity-base algebra extensions along g^♯

Tensor-hom adjunction together with the same-site identifications
NL_{g⁻¹ O_C / g⁻¹ f⁻¹ O_B} = g⁻¹ NL_{O_C / O_B} and
Lg^* NL_{O_C / O_B} = g⁻¹ NL_{O_C / O_B} ⊗^L_{g⁻¹ O_C} O_D
identifies Ext¹_{g⁻¹ O_C}(NL, G) with Ext¹_{O_D}(Lg^* NL, G).
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
variable {G : SheafOfModules (ringSheaf J O_D)}

/-- Derived counit `Lg^* (restriction G)[0] ⟶ G[0]`, as `coeffDerived` of the
extension-restriction counit. -/
def restrictCounit (gSharp : O_C ⟶ O_D) (G : SheafOfModules (ringSheaf J O_D)) :
    (SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj
          ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G))) ⟶
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G) :=
  coeffDerived ((extendRestrictAdj gSharp).counit.app G)

/-- `restrictCounit` is `coeffDerived` of the extension-restriction counit. -/
theorem restrictCounit_spec (gSharp : O_C ⟶ O_D) (G : SheafOfModules (ringSheaf J O_D)) :
    restrictCounit gSharp G =
      coeffDerived ((extendRestrictAdj gSharp).counit.app G) := sorry

/-- Forward map of the displayed Ext¹ identification, sending a class along `Lg^*`
and the derived counit. -/
def extOne_restrict (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D))
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj
          ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G)))) :
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  ShiftedHom.comp
    ((SameSite.pullbackDerived gSharp).map ξ ≫
      ((SameSite.pullbackDerived gSharp).commShiftIso (1 : ℤ)).hom.app
        ((moduleQ O_C).obj
          ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G))))
    (ShiftedHom.mk₀ (0 : ℤ) rfl (restrictCounit gSharp G)) (zero_add (1 : ℤ))

/-- Derived unit `F[0] ⟶ restriction (g^* F)[0]`, as `moduleQ` of the
extension-restriction unit, dual to `restrictCounit`. -/
def restrictUnit (gSharp : O_C ⟶ O_D) (F : SheafOfModules (ringSheaf J O_C)) :
    (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F) ⟶
      (moduleQ O_C).obj
        ((CochainComplex.singleFunctor _ 0).obj
          ((restrictionAlong gSharp).obj ((extendAlong gSharp).obj F))) :=
  (moduleQ O_C).map
    ((CochainComplex.singleFunctor
        (ringedSiteModuleCategory.{u, u, u, u} J O_C) 0).map
      ((extendRestrictAdj gSharp).unit.app F))

/-- `restrictUnit` is `moduleQ` of the extension-restriction unit in degree `0`. -/
theorem restrictUnit_spec (gSharp : O_C ⟶ O_D) (F : SheafOfModules (ringSheaf J O_C)) :
    restrictUnit gSharp F =
      (moduleQ O_C).map
        ((CochainComplex.singleFunctor
            (ringedSiteModuleCategory.{u, u, u, u} J O_C) 0).map
          ((extendRestrictAdj gSharp).unit.app F)) := sorry

/-- Degree `0` comparison `restriction (G[0]) ⟶ (restriction G)[0]` in the derived
category, as `mapDerivedCategoryFactors` followed by `singleMapHomologicalComplex`. -/
def extOne_restrict_coeffComparison (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D)) :
    (restrictionAlong gSharp).mapDerivedCategory.obj
        ((moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) ⟶
      (moduleQ O_C).obj
        ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G)) :=
  (restrictionAlong gSharp).mapDerivedCategoryFactors.hom.app
      ((CochainComplex.singleFunctor _ 0).obj G) ≫
    (moduleQ O_C).map
      ((HomologicalComplex.singleMapHomologicalComplex
          (restrictionAlong gSharp) (ComplexShape.up ℤ) (0 : ℤ)).hom.app G)

/-- `extOne_restrict_coeffComparison` is `mapDerivedCategoryFactors` followed by
the single-complex comparison for restriction. -/
theorem extOne_restrict_coeffComparison_spec (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D)) :
    extOne_restrict_coeffComparison gSharp G =
      (restrictionAlong gSharp).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor _ 0).obj G) ≫
        (moduleQ O_C).map
          ((HomologicalComplex.singleMapHomologicalComplex
              (restrictionAlong gSharp) (ComplexShape.up ℤ) (0 : ℤ)).hom.app G) :=
  sorry

/-- Same-site `Lg^*`, as the homotopy total left derived functor of module pullback. -/
def pullbackDerivedFunctor (gSharp : O_C ⟶ O_D) :
    DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O_C) ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O_D) :=
  Functor.LeftDerived.Homotopy.functor ((sameSiteHom gSharp).modulePullback)

/-- `pullbackDerivedFunctor` is the homotopy total left derived functor of module pullback. -/
theorem pullbackDerivedFunctor_spec (gSharp : O_C ⟶ O_D) :
    pullbackDerivedFunctor gSharp =
      Functor.LeftDerived.Homotopy.functor ((sameSiteHom gSharp).modulePullback) :=
  sorry

/-- Cochain-level comparison `Q ⋙ Lg^* ⟶ extendComplex ⋙ Q` along `g^♯`. -/
def pullbackDerivedCochainCounit (gSharp : O_C ⟶ O_D) :
    moduleQ O_C ⋙ pullbackDerivedFunctor gSharp ⟶
      extendComplex gSharp ⋙ moduleQ O_D :=
  Functor.LeftDerived.Homotopy.cochainCounit
      ((sameSiteHom gSharp).modulePullback) ≫
    Functor.whiskerRight (pullbackComplexExtendIso gSharp).hom (moduleQ O_D)

/-- `pullbackDerivedCochainCounit` is the cochain counit of module pullback, compared
by `pullbackComplexExtendIso`. -/
theorem pullbackDerivedCochainCounit_spec (gSharp : O_C ⟶ O_D) :
    pullbackDerivedCochainCounit gSharp =
      Functor.LeftDerived.Homotopy.cochainCounit
          ((sameSiteHom gSharp).modulePullback) ≫
        Functor.whiskerRight (pullbackComplexExtendIso gSharp).hom (moduleQ O_D) :=
  sorry

/-- Derived comparison `Lg^* Q NL ⟶ Q (g^* NL)` at the naive cotangent complex. -/
def restrictCounitNL (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    (SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ⟶
      (moduleQ O_D).obj
        ((extendComplex gSharp).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) :=
  (Functor.LeftDerived.Homotopy.cochainCounit
        ((sameSiteHom gSharp).modulePullback)).app
      (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
    (moduleQ O_D).map
      ((pullbackComplexExtendIso gSharp).hom.app
        (NaiveCotangent.obj O_B (Under.mk fSharp)))

/-- `restrictCounitNL` is the cochain counit of module pullback, compared by
`pullbackComplexExtendIso`. -/
theorem restrictCounitNL_spec (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    restrictCounitNL fSharp gSharp =
      (Functor.LeftDerived.Homotopy.cochainCounit
            ((sameSiteHom gSharp).modulePullback)).app
          (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
        (moduleQ O_D).map
          ((pullbackComplexExtendIso gSharp).hom.app
            (NaiveCotangent.obj O_B (Under.mk fSharp))) := sorry

/-- `Lg^*` is a left-derived functor of same-site extension of scalars, via
`pullbackDerivedCochainCounit`. -/
instance pullbackDerived_isLeftDerived (gSharp : O_C ⟶ O_D) :
    (pullbackDerivedFunctor gSharp).IsLeftDerivedFunctor
      (pullbackDerivedCochainCounit gSharp)
      (HomologicalComplex.quasiIso
        (ringedSiteModuleCategory.{u, u, u, u} J O_C) (ComplexShape.up ℤ)) :=
  sorry

/-- Restriction on derived categories is a right-derived functor of complex-level
restriction, via `mapDerivedCategoryFactors.inv`. -/
instance restrictionMapDerived_isRightDerived (gSharp : O_C ⟶ O_D) :
    (restrictionAlong gSharp).mapDerivedCategory.IsRightDerivedFunctor
      (restrictionAlong gSharp).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso
        (ringedSiteModuleCategory.{u, u, u, u} J O_D) (ComplexShape.up ℤ)) :=
  sorry

/-- The composite `Lg^* ⋙ restriction` remains left-derived, as needed to form the
derived extend-restrict adjunction. -/
instance pullbackDerived_restriction_isLeftDerived (gSharp : O_C ⟶ O_D) :
    (pullbackDerivedFunctor gSharp ⋙
        (restrictionAlong gSharp).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator (moduleQ O_C) (pullbackDerivedFunctor gSharp)
            (restrictionAlong gSharp).mapDerivedCategory).inv ≫
        Functor.whiskerRight (pullbackDerivedCochainCounit gSharp)
          (restrictionAlong gSharp).mapDerivedCategory)
      (HomologicalComplex.quasiIso
        (ringedSiteModuleCategory.{u, u, u, u} J O_C) (ComplexShape.up ℤ)) :=
  sorry

/-- The composite `restriction ⋙ Lg^*` remains right-derived, as needed to form the
derived extend-restrict adjunction. -/
instance restriction_pullbackDerived_isRightDerived (gSharp : O_C ⟶ O_D) :
    ((restrictionAlong gSharp).mapDerivedCategory ⋙
        pullbackDerivedFunctor gSharp).IsRightDerivedFunctor
      (Functor.whiskerRight (restrictionAlong gSharp).mapDerivedCategoryFactors.inv
          (pullbackDerivedFunctor gSharp) ≫
        (Functor.associator (moduleQ O_D) (restrictionAlong gSharp).mapDerivedCategory
          (pullbackDerivedFunctor gSharp)).hom)
      (HomologicalComplex.quasiIso
        (ringedSiteModuleCategory.{u, u, u, u} J O_D) (ComplexShape.up ℤ)) :=
  sorry

/-- Derived extension of scalars is left adjoint to derived restriction of scalars. -/
def extendRestrictDerivedAdj (gSharp : O_C ⟶ O_D) :
    pullbackDerivedFunctor gSharp ⊣ (restrictionAlong gSharp).mapDerivedCategory :=
  Adjunction.derived
    (Adjunction.mapHomologicalComplexAdjunction (extendRestrictAdj gSharp)
      (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso
      (ringedSiteModuleCategory.{u, u, u, u} J O_C) (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso
      (ringedSiteModuleCategory.{u, u, u, u} J O_D) (ComplexShape.up ℤ))
    (pullbackDerivedCochainCounit gSharp)
    (restrictionAlong gSharp).mapDerivedCategoryFactors.inv

/-- `extendRestrictDerivedAdj` is the derived adjunction of `extendRestrictAdj`. -/
theorem extendRestrictDerivedAdj_spec (gSharp : O_C ⟶ O_D) :
    extendRestrictDerivedAdj gSharp =
      Adjunction.derived
        (Adjunction.mapHomologicalComplexAdjunction (extendRestrictAdj gSharp)
          (ComplexShape.up ℤ))
        (HomologicalComplex.quasiIso
          (ringedSiteModuleCategory.{u, u, u, u} J O_C) (ComplexShape.up ℤ))
        (HomologicalComplex.quasiIso
          (ringedSiteModuleCategory.{u, u, u, u} J O_D) (ComplexShape.up ℤ))
        (pullbackDerivedCochainCounit gSharp)
        (restrictionAlong gSharp).mapDerivedCategoryFactors.inv :=
  sorry

/-- Derived unit `Q NL ⟶ restriction (Lg^* Q NL)` at the naive cotangent complex. -/
def restrictUnitNL (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    (moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)) ⟶
      (restrictionAlong gSharp).mapDerivedCategory.obj
        ((SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)))) :=
  (extendRestrictDerivedAdj gSharp).unit.app
    ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)))

/-- `restrictUnitNL` is the derived extend-restrict unit at `Q NL`. -/
theorem restrictUnitNL_spec (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    restrictUnitNL fSharp gSharp =
      (extendRestrictDerivedAdj gSharp).unit.app
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) :=
  sorry

/-- Reverse map of the displayed Ext¹ identification, as the reverse tensor-hom map:
restriction of the class, compared by `commShiftIso`, then precomposition with the
derived unit of `extendRestrictDerivedAdj`. -/
def extOne_restrict_symm (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D))
    (ζ :
      Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
        (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O_C).obj
        ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G))) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (restrictUnitNL fSharp gSharp))
    (ShiftedHom.comp
      (ζ.map (restrictionAlong gSharp).mapDerivedCategory)
      (ShiftedHom.mk₀ (0 : ℤ) rfl (extOne_restrict_coeffComparison gSharp G))
      (zero_add (1 : ℤ)))
    (add_zero (1 : ℤ))

/-- Tensor-hom adjunction plus the two naive-cotangent identifications, as an
equivalence
`Ext¹_{O_C}(NL_{O_C/O_B}, restriction G) ≃ Ext¹_{O_D}(Lg^* NL_{O_C/O_B}, G)`. -/
def extOne_restrictEquiv (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D)) :
    Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj
          ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G))) ≃
      Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
        (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) where
  toFun := extOne_restrict fSharp gSharp G
  invFun := extOne_restrict_symm fSharp gSharp G
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extOne_restrictEquiv` is `extOne_restrict`. -/
theorem extOne_restrictEquiv_apply (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D))
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj
          ((CochainComplex.singleFunctor _ 0).obj ((restrictionAlong gSharp).obj G)))) :
    extOne_restrictEquiv fSharp gSharp G ξ =
      extOne_restrict fSharp gSharp G ξ := sorry

/-- The reverse map of `extOne_restrictEquiv` is `extOne_restrict_symm`. -/
theorem extOne_restrictEquiv_symm_apply (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D))
    (ζ :
      Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
        (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    (extOne_restrictEquiv fSharp gSharp G).symm ζ =
      extOne_restrict_symm fSharp gSharp G ζ := sorry

/-- `extOne_restrictEquiv` identifies the two Ext¹ groups of the source display. -/
theorem extOne_restrictEquiv_spec (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (G : SheafOfModules (ringSheaf J O_D)) :
    (extOne_restrictEquiv fSharp gSharp G).toFun =
      extOne_restrict fSharp gSharp G := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
