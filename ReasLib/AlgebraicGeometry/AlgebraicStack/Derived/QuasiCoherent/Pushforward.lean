/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Plus
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.FppfHigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Homology
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open scoped Bicategory

noncomputable section

universe u

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard

-- Local instance justification (defeq pin): homotopy-to-derived direct image must select the canonical additivity certificate for the concrete fppf module direct image.
attribute [local instance 2000] instFppfModulePushforwardAdditive

-- Local instance justification (defeq pin): the canonical derived model uses this ordinary-derivability certificate rather than the one inferred from pointwise existence.
attribute [local instance 2000] fppfModulePushforwardHasRightDerived

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Bounded-below `Rf_*` preserves `D⁺_{LQCoh^{fbc}}`. -/
theorem mapsTo_plus_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Plus.cohomologyIn (FppfModules.lqcohFbc X) ≤
      (Plus.cohomologyIn (FppfModules.lqcohFbc Y)).inverseImage
        (moduleDerivedPushforwardPlus f) := sorry

/-- Derived direct image on bounded-below fppf modules with `LQCoh^{fbc}` cohomology. -/
def derivedPushforwardPlusLQCohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedLQCohFbc.Plus X ⥤ DerivedLQCohFbc.Plus Y :=
  FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_lqcohFbc f)

/-- Right commuting square: restriction to `D⁺_{LQCoh^{fbc}}` whiskers with
the inclusions into `D⁺(𝒪)`. -/
def derivedPushforwardPlusLQCohFbc_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.inclusion Y ≅
      DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f :=
  FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_lqcohFbc f)

/-- Derived direct image on coefficients: `Rf_*` on `D⁺_{LQCoh^{fbc}}` whiskers
with the ambient inclusions into unbounded `D(𝒪)`. -/
def derivedPushforwardPlusLQCohFbc_comp_ambient {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ≅
      DerivedLQCohFbc.Plus.ambient X ⋙ moduleDerivedPushforward f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedPushforwardPlusLQCohFbc_comp_inclusion f)
      Plus.ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedLQCohFbc.Plus.inclusion X)
      (moduleDerivedPushforwardPlus_comp_ι f)

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` commutes with shifts. -/
instance derivedPushforwardPlusLQCohFbc.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusLQCohFbc f).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (derivedPushforwardPlusLQCohFbc_comp_inclusion f) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ inferInstance inferInstance inferInstance
      (DerivedLQCohFbc.Plus.inclusion X) (moduleDerivedPushforwardPlus f) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (moduleDerivedPushforwardPlus.instCommShift f))

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` is triangulated. -/
instance derivedPushforwardPlusLQCohFbc.instIsTriangulated
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusLQCohFbc f).IsTriangulated := sorry

/-- Bounded-below `Rf_*` preserves `D⁺_{Parasitic ∩ LQCoh^{fbc}}`. -/
theorem mapsTo_plus_parasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X) ≤
      (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc Y)).inverseImage
        (moduleDerivedPushforwardPlus f) := sorry

/-- Derived direct image on bounded-below fppf modules with parasitic `LQCoh^{fbc}` cohomology. -/
def derivedPushforwardPlusParasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedParasiticLQCohFbcPlus X ⥤ derivedParasiticLQCohFbcPlus Y :=
  FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_parasitic f)

/-- Left commuting square: restriction to parasitic plus objects whiskers with
the inclusions into `D⁺(𝒪)`. -/
def derivedPushforwardPlusParasitic_comp_ι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic f ⋙
        (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc Y)).ι ≅
      (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X)).ι ⋙
        moduleDerivedPushforwardPlus f :=
  FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_parasitic f)

/-- Derived direct image on parasitic coefficients: `Rf_*` on parasitic plus objects
whiskers with the inclusions into `D⁺_{LQCoh^{fbc}}`. -/
def derivedPushforwardPlusParasitic_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic f ⋙
        derivedParasiticLQCohFbcPlus.inclusion Y ≅
      derivedParasiticLQCohFbcPlus.inclusion X ⋙
        derivedPushforwardPlusLQCohFbc f :=
  ((Plus.cohomologyIn (FppfModules.lqcohFbc Y)).fullyFaithfulι.whiskeringRight
      (derivedParasiticLQCohFbcPlus X)).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedPushforwardPlusParasitic f)
        (Plus.CohomologyIn.inclusion.compιIso
          ((inf_le_right : FppfModules.parasiticLQCohFbc Y ≤ FppfModules.lqcohFbc Y))) ≪≫
      derivedPushforwardPlusParasitic_comp_ι f ≪≫
      Functor.isoWhiskerRight
        (Plus.CohomologyIn.inclusion.compιIso
          ((inf_le_right : FppfModules.parasiticLQCohFbc X ≤ FppfModules.lqcohFbc X))).symm
        (moduleDerivedPushforwardPlus f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedParasiticLQCohFbcPlus.inclusion X)
        (derivedPushforwardPlusLQCohFbc_comp_inclusion f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- Restricted `Rf_*` on parasitic plus objects commutes with shifts. -/
instance derivedPushforwardPlusParasitic.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusParasitic f).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
    (derivedPushforwardPlusParasitic_comp_ι f) inferInstance inferInstance ℤ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Functor.CommShift.comp _ _ _ inferInstance inferInstance inferInstance
      ((Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X)).ι) (moduleDerivedPushforwardPlus f) ℤ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (moduleDerivedPushforwardPlus.instCommShift f))

/-- Restricted `Rf_*` on parasitic plus objects is triangulated. -/
instance derivedPushforwardPlusParasitic.instIsTriangulated
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusParasitic f).IsTriangulated := sorry

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` sends parasitic plus objects to
parasitic plus objects. -/
theorem derivedPushforwardPlusLQCohFbc_maps_parasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedParasiticPlus X ≤
      (derivedParasiticPlus Y).inverseImage
        (derivedPushforwardPlusLQCohFbc f) := sorry

/-- A single object in `D⁺(𝒪_X)` built from an fppf `LQCoh^{fbc}` module has
cohomology in `lqcohFbc`. -/
theorem singleFunctor_maps_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    FppfModules.lqcohFbc X ≤
      (Plus.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (DerivedCategory.Plus.singleFunctor (fppfModules X) n) := sorry

/-- Degree-`n` single-object functor into `D⁺_{LQCoh^{fbc}}(𝒪_X)`. -/
def DerivedLQCohFbc.Plus.singleFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    FppfModules.LQCohFbc X ⥤ DerivedLQCohFbc.Plus X :=
  FullSubcategory.restrict (DerivedCategory.Plus.singleFunctor (fppfModules X) n)
    (singleFunctor_maps_lqcohFbc X n)

/-- Forgetful comparison of the plus `LQCoh^{fbc}` single functor with the
ambient plus single functor. -/
def DerivedLQCohFbc.Plus.singleFunctor_comp_inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    DerivedLQCohFbc.Plus.singleFunctor X n ⋙ DerivedLQCohFbc.Plus.inclusion X ≅
      FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) n :=
  FullSubcategory.restrict.compιIso
    (DerivedCategory.Plus.singleFunctor (fppfModules X) n)
    (singleFunctor_maps_lqcohFbc X n)

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

variable {S : Scheme.{u}}

/-- Composite of plus `Rf_*` on `LQCoh^{fbc}` with the plus Verdier quotient
functor on the target. -/
def pushforwardToPlus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedLQCohFbc.Plus X ⥤ DerivedQCoh.Plus Y :=
  derivedPushforwardPlusLQCohFbc f ⋙ DerivedQCoh.Plus.quotientFunctor Y

/-- The composite through `D⁺_QCoh(𝒪_Y)` inverts the plus parasitic Verdier
system. -/
theorem pushforwardToPlus_inverts {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedParasiticPlus X).trW.IsInvertedBy (pushforwardToPlus f) := sorry

/-- `pushforwardToPlus` commutes with shifts. -/
instance pushforwardToPlus.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforwardToPlus f).CommShift ℤ :=
  inferInstanceAs
    ((derivedPushforwardPlusLQCohFbc f ⋙
        DerivedQCoh.Plus.quotientFunctor Y).CommShift ℤ)

/-- `pushforwardToPlus` is triangulated. -/
instance pushforwardToPlus.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    @Functor.IsTriangulated _ _ _ _ _ _ (pushforwardToPlus f) inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance
      (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n)
      inferInstance inferInstance := sorry

/-- Derived quasi-coherent pushforward
`Rf_{QCoh,*} : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(𝒪_Y)`. -/
def pushforward {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus Y :=
  @VerdierQuotient.Exact.factor
    _ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (derivedParasiticPlus X) _ inferInstance inferInstance inferInstance inferInstance
    (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n) inferInstance
    (pushforwardToPlus f) (pushforwardToPlus.instCommShift f)
    (pushforwardToPlus.instIsTriangulated f)
    (pushforwardToPlus_inverts f)

/-- Canonical comparison from the plus quotient functor followed by
`pushforward` to `pushforwardToPlus`. -/
def pushforward_facIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus.quotientFunctor X ⋙ pushforward f ≅
      pushforwardToPlus f :=
  @VerdierQuotient.Exact.factor.facIso
    _ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (derivedParasiticPlus X) _ inferInstance inferInstance inferInstance inferInstance
    (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n) inferInstance
    (pushforwardToPlus f) (pushforwardToPlus.instCommShift f)
    (pushforwardToPlus.instIsTriangulated f)
    (pushforwardToPlus_inverts f)

/-- Strict factorization of `pushforward` through the plus quotient functor. -/
theorem pushforward_fac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus.quotientFunctor X ⋙ pushforward f =
      pushforwardToPlus f := sorry

/-- `Rf_{QCoh,*}` commutes with shifts. -/
instance pushforward.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforward f).CommShift ℤ :=
  @VerdierQuotient.Exact.factor.commShift
    _ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (derivedParasiticPlus X) _ inferInstance inferInstance inferInstance inferInstance
    (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n) inferInstance
    inferInstance
    (pushforwardToPlus f) (pushforwardToPlus.instCommShift f)
    (pushforwardToPlus.instIsTriangulated f)
    (pushforwardToPlus_inverts f)

/-- `Rf_{QCoh,*}` is triangulated. -/
instance pushforward.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    @Functor.IsTriangulated _ _ _ _ _ _ (pushforward f) inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus X) n)
      (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n)
      inferInstance inferInstance :=
  @VerdierQuotient.Exact.factor.isTriangulated
    _ inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (derivedParasiticPlus X) _ inferInstance inferInstance inferInstance inferInstance
    (fun n => VerdierQuotient.shiftAdditive (derivedParasiticPlus Y) n) inferInstance
    inferInstance inferInstance
    (pushforwardToPlus f) (pushforwardToPlus.instCommShift f)
    (pushforwardToPlus.instIsTriangulated f)
    (pushforwardToPlus_inverts f)

/-- Place a quasi-coherent module in degree zero in `D⁺_QCoh(𝒪_X)`. -/
def singlePlus (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ DerivedQCoh.Plus X :=
  QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
    DerivedQCoh.Plus.quotientFunctor X

-- Local declaration justification (metaprogramming implementation): private comparison implementations must be exported for the exposed public cohomology comparison.
set_option backward.privateInPublic true

/-- Reduce `H^i ∘ inclusion ∘ Rf_{QCoh,*} ∘ singlePlus` along
`pushforward_facIso`. -/
private def homology_pushforward_single_pushforwardFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        pushforwardToPlus f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0)
    (isoWhiskerRight (pushforward_facIso f)
      (Plus.inclusion Y ⋙ homologyFunctor Y i))

/-- Reduce the plus-quotient factorization of `Rf_{QCoh,*}` along
`Plus.inclusion_facIso`. -/
private def homology_pushforward_single_inclusionFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        pushforwardToPlus f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ Plus.toUnboundedComposite Y ⋙
          homologyFunctor Y i :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f)
    (isoWhiskerRight (Plus.inclusion_facIso Y) (homologyFunctor Y i))

/-- Reduce `H^i` along `homologyFunctor_comp_quotientFunctor`. -/
private def homology_pushforward_single_homologyFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ Plus.toUnboundedComposite Y ⋙
          homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y i :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y)
    (homologyFunctor_comp_quotientFunctor Y i)

/-- Composite of the three factorization comparisons reducing
`H^i ∘ inclusion ∘ Rf_{QCoh,*} ∘ singlePlus` to degree-zero homology of
plus `Rf_*` after `homologyToQCoh`. -/
private def homology_pushforward_single_reduce {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y i :=
  homology_pushforward_single_pushforwardFac f i ≪≫
    homology_pushforward_single_inclusionFac f i ≪≫
    homology_pushforward_single_homologyFac f i

/-- Forget lifted cohomology of plus `Rf_*` on a degree-zero object. -/
private def homology_underlying_compι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ⋙
          FppfModules.inclusion Y ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).ι ⋙
            DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y)
    (DerivedCategory.CohomologyIn.Homology.compιIso
      (FppfModules.lqcohFbc Y) (i : ℤ))

/-- Replace `toUnbounded ⋙ cohomologyIn.ι` by the ambient plus inclusion. -/
private def homology_underlying_toAmbient {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).ι ⋙
            DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ⋙
          DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f)
    (isoWhiskerRight
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
        (FppfModules.lqcohFbc Y))
      (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace plus `Rf_*` followed by the ambient inclusion with the plus-level
restriction comparison. -/
private def homology_underlying_plusInclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ⋙
          DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0)
    (isoWhiskerRight (derivedPushforwardPlusLQCohFbc_comp_inclusion f)
      (DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace the plus `LQCoh^{fbc}` single functor by the ambient plus single
functor. -/
private def homology_underlying_singleInclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
          moduleDerivedPushforwardPlus f ⋙
            DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X)
    (isoWhiskerRight (DerivedLQCohFbc.Plus.singleFunctor_comp_inclusion X 0)
      (moduleDerivedPushforwardPlus f ⋙
        DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace plus homology of `Rf_*` on a degree-zero object by ordinary
`R^i f_*`. -/
private def homology_underlying_rightDerived {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
          moduleDerivedPushforwardPlus f ⋙
            DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.inclusion X ⋙
        (fppfModulePushforward f).rightDerived i :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X)
    (moduleDerivedPushforwardPlus.singleHomologyIso f i)

/-- Underlying comparison from plus `LQCoh^{fbc}` homology of `Rf_*` on a
degree-zero object to ordinary fppf `R^i f_*`. -/
private def homology_fppfModuleDerivedPushforward_single_underlying
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ⋙
          FppfModules.inclusion Y ≅
      QCoh.inclusion X ⋙
        (fppfModulePushforward f).rightDerived i :=
  homology_underlying_compι f i ≪≫
    homology_underlying_toAmbient f i ≪≫
    homology_underlying_plusInclusion f i ≪≫
    homology_underlying_singleInclusion f i ≪≫
    homology_underlying_rightDerived f i

/-- `QCoh.higherDirectImageToLQCohFbc` is the lift of the underlying homology comparison
target. -/
private def homology_fppfModuleDerivedPushforward_single_lqcoh
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ≅
      QCoh.higherDirectImageToLQCohFbc f i :=
  (FppfModules.lqcohFbc Y).liftNatIso
    (fun F => ((DerivedCategory.CohomologyIn.Homology.functor
      (FppfModules.lqcohFbc Y) (i : ℤ)).obj
        ((QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
          derivedPushforwardPlusLQCohFbc f ⋙
            DerivedLQCohFbc.Plus.toUnbounded Y).obj F)).property)
    (QCoh.higherDirectImage_mem_lqcohFbc f i)
    (homology_fppfModuleDerivedPushforward_single_underlying f i)

/-- Named bridge from degree-zero homology of fppf `Rf_*` after `toQCoh` to
ordinary fppf `R^i f_*` after `toQCoh`. -/
private def homology_fppfModuleDerivedPushforward_single {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y (i : ℤ) ≅
      QCoh.higherDirectImageToLQCohFbc f i ⋙ FppfModules.LQCohFbc.toQCoh Y :=
  isoWhiskerRight (homology_fppfModuleDerivedPushforward_single_lqcoh f i)
    (FppfModules.LQCohFbc.toQCoh Y)

/-- Cohomology of bounded-below quasi-coherent derived direct image on a module
placed in degree zero is quasi-coherent higher direct image. -/
def cohomology_pushforward_single_iso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙
        cohomologyFunctor Y (i : ℤ) ≅ QCoh.higherDirectImageFunctor f i :=
  isoWhiskerRight (homology_pushforward_single_reduce f i ≪≫
      homology_fppfModuleDerivedPushforward_single f i)
      (FppfModules.LQCohFbc.quotientToQCoh Y) ≪≫
    isoWhiskerLeft (QCoh.higherDirectImageToLQCohFbc f i)
      (FppfModules.LQCohFbc.toQCoh_comp_quotientToQCoh Y) ≪≫
    eqToIso (QCoh.higherDirectImageToLQCohFbc_comp_coreflector f i)

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh

