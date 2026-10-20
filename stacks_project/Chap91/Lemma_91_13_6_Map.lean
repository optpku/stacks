/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import stacks_project.Chap91.Lemma_91_13_1_Obstruction

/-!
# Functoriality of derived Ext¹ along same-site pullback and coefficient maps

The maps `Lg^*` and `Lg^* F[0] ⟶ G[0]` induced by `gSharp` and an
`O_D`-linear coefficient map `c` act on `Ext⁽1⁾(Q NL, Q(F[0]))`, while
precomposition along `Lg^* NL_{O_C/O_B} ⟶ NL_{O_D/O_B}` acts on
`Ext⁽1⁾(Q NL_{O_D/O_B}, Q(G[0]))`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
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

/-- Canonical homology on same-site module sheaves, unlocking `pullbackDerived.commShift`. -/
instance instCategoryWithHomology (O : Sheaf J CommRingCat.{u}) :
    CategoryWithHomology
      (RingedSite.ModuleCat.{u} (RingedSite.ofCommRingSheaf J O)) :=
  RingedSite.ModuleCat.categoryWithHomology (RingedSite.ofCommRingSheaf J O)

/-- Derived-to-underived comparison `Lg^* NL_{O_C/O_B} ⟶ NL_{O_D/O_B}` along the
identity-base square `𝟙 O_B`, `fSharp`, `fSharp ≫ gSharp`, `gSharp`. -/
def naiveCotangentComparison (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    (SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))) ⟶
      (moduleQ O_D).obj (NaiveCotangent.obj O_B (Under.mk (fSharp ≫ gSharp))) :=
  (Functor.LeftDerived.Homotopy.cochainCounit
        ((sameSiteHom gSharp).modulePullback)).app
      (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
    (moduleQ O_D).map
      ((pullbackComplexExtendIso gSharp).hom.app
          (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
        NaiveCotangent.map
          (⟨Category.id_comp (fSharp ≫ gSharp)⟩ :
            CommSq (𝟙 O_B) fSharp (fSharp ≫ gSharp) gSharp))

/-- `naiveCotangentComparison` is the cochain counit of module pullback at
`NL(fSharp)`, followed by `moduleQ.map` of the identity-base naive cotangent map. -/
theorem naiveCotangentComparison_spec (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    naiveCotangentComparison fSharp gSharp =
      (Functor.LeftDerived.Homotopy.cochainCounit
            ((sameSiteHom gSharp).modulePullback)).app
          (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
        (moduleQ O_D).map
          ((pullbackComplexExtendIso gSharp).hom.app
              (NaiveCotangent.obj O_B (Under.mk fSharp)) ≫
            NaiveCotangent.map
              (⟨Category.id_comp (fSharp ≫ gSharp)⟩ :
                CommSq (𝟙 O_B) fSharp (fSharp ≫ gSharp) gSharp)) := sorry

variable {F : SheafOfModules (ringSheaf J O_C)}
variable {G : SheafOfModules (ringSheaf J O_D)}

/-- Derived-to-underived comparison `Lg^* F[0] ⟶ G[0]` along `c : g^* F ⟶ G`. -/
def coeffDerived {gSharp : O_C ⟶ O_D} (c : (extendAlong gSharp).obj F ⟶ G) :
    (SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F)) ⟶
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G) :=
  (Functor.LeftDerived.Homotopy.cochainCounit
        ((sameSiteHom gSharp).modulePullback)).app
      ((CochainComplex.singleFunctor _ 0).obj F) ≫
    (moduleQ O_D).map
      ((HomologicalComplex.singleMapHomologicalComplex
            ((sameSiteHom gSharp).modulePullback) (ComplexShape.up ℤ) (0 : ℤ)).hom.app F ≫
        (CochainComplex.singleFunctor
            (ringedSiteModuleCategory.{u, u, u, u} J O_D) 0).map
          ((pullbackExtendIso gSharp).hom.app F ≫ c))

/-- `coeffDerived` is the cochain counit at `F[0]`, followed by `moduleQ.map` of
the single-complex comparison along `c`. -/
theorem coeffDerived_spec {gSharp : O_C ⟶ O_D} (c : (extendAlong gSharp).obj F ⟶ G) :
    coeffDerived c =
      (Functor.LeftDerived.Homotopy.cochainCounit
            ((sameSiteHom gSharp).modulePullback)).app
          ((CochainComplex.singleFunctor _ 0).obj F) ≫
        (moduleQ O_D).map
          ((HomologicalComplex.singleMapHomologicalComplex
                ((sameSiteHom gSharp).modulePullback)
                (ComplexShape.up ℤ) (0 : ℤ)).hom.app F ≫
            (CochainComplex.singleFunctor
                (ringedSiteModuleCategory.{u, u, u, u} J O_D) 0).map
              ((pullbackExtendIso gSharp).hom.app F ≫ c)) := sorry

/-- The covariant map `Ext⁽1⁾(Q NL_C, Q F[0]) → Ext⁽1⁾(Lg^* NL_C, Lg^* F[0])`
induced by `SameSite.pullbackDerived gSharp`. -/
def extOne_pullback {fSharp : O_B ⟶ O_C} (gSharp : O_C ⟶ O_D)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      (SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) :=
  (SameSite.pullbackDerived gSharp).map ξ ≫
    ((SameSite.pullbackDerived gSharp).commShiftIso (1 : ℤ)).hom.app
      ((moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))

/-- `extOne_pullback` is `Lg^*` on the Ext class, compared by `commShiftIso 1`. -/
theorem extOne_pullback_apply {fSharp : O_B ⟶ O_C} (gSharp : O_C ⟶ O_D)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    extOne_pullback gSharp ξ =
      (SameSite.pullbackDerived gSharp).map ξ ≫
        ((SameSite.pullbackDerived gSharp).commShiftIso (1 : ℤ)).hom.app
          ((moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F)) := sorry

/-- Postcomposition `Ext⁽1⁾(Lg^* NL_C, Lg^* F[0]) → Ext⁽1⁾(Lg^* NL_C, Q G[0])`
along `coeffDerived c`. -/
def extOne_postcomp {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
    (c : (extendAlong gSharp).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
        (SameSite.pullbackDerived gSharp).obj
          ((moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F)))) :
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  ShiftedHom.comp ξ (ShiftedHom.mk₀ (0 : ℤ) rfl (coeffDerived c)) (zero_add (1 : ℤ))

/-- The composite `Ext⁽1⁾(Q NL_C, Q F[0]) → Ext⁽1⁾(Lg^* NL_C, Q G[0])` sending
ξ along `Lg^*` and then along `Lg^* F ⟶ g^* F ⟶ G`. -/
def extOne_map {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
    (c : (extendAlong gSharp).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  extOne_postcomp c (extOne_pullback gSharp ξ)

/-- `extOne_map` is pullback along `Lg^*` followed by postcomposition along `c`. -/
theorem extOne_map_spec {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
    (c : (extendAlong gSharp).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
        (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    extOne_map c ξ = extOne_postcomp c (extOne_pullback gSharp ξ) := sorry

/-- The zero Ext¹ class is sent to zero under `extOne_map`. -/
theorem extOne_map_zero {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
    (c : (extendAlong gSharp).obj F ⟶ G) :
    extOne_map c (0 :
        Ext⁽(1 : ℤ)⁾((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
          (moduleQ O_C).obj ((CochainComplex.singleFunctor _ 0).obj F))) = 0 :=
  sorry

/-- Precomposition `Ext⁽1⁾(Q NL_D, Q G[0]) → Ext⁽1⁾(Lg^* NL_C, Q G[0])` along
`naiveCotangentComparison`. -/
def extOne_comap (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_D).obj (NaiveCotangent.obj O_B (Under.mk (fSharp ≫ gSharp))),
        (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((SameSite.pullbackDerived gSharp).obj
        ((moduleQ O_C).obj (NaiveCotangent.obj O_B (Under.mk fSharp))),
      (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (naiveCotangentComparison fSharp gSharp)) ζ
    (add_zero (1 : ℤ))

/-- `extOne_comap` is precomposition along `naiveCotangentComparison`. -/
theorem extOne_comap_spec (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D)
    (ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ O_D).obj (NaiveCotangent.obj O_B (Under.mk (fSharp ≫ gSharp))),
        (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    extOne_comap fSharp gSharp ζ =
      ShiftedHom.comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (naiveCotangentComparison fSharp gSharp)) ζ
        (add_zero (1 : ℤ)) := sorry

/-- The zero Ext¹ class is sent to zero under `extOne_comap`. -/
theorem extOne_comap_zero (fSharp : O_B ⟶ O_C) (gSharp : O_C ⟶ O_D) :
    extOne_comap fSharp gSharp (0 :
        Ext⁽(1 : ℤ)⁾((moduleQ O_D).obj (NaiveCotangent.obj O_B (Under.mk (fSharp ≫ gSharp))),
          (moduleQ O_D).obj ((CochainComplex.singleFunctor _ 0).obj G))) = 0 :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening
