/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.EtaleFppf
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact

/-! # Étale–fppf comparison on derived quasi-coherent modules -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Derived inverse image `ε^* : D(X_étale, 𝒪_X) ⥤ D(𝒪_X)`. -/
abbrev etaleFppfInverseImageDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerivedEtale X ⥤ ModuleDerived X :=
  ExactFunctor.mapDerivedCategory (etaleFppfInverseImageExact X)

/-- Derived `ε^*` commutes with shifts. -/
instance etaleFppfInverseImageDerived.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerived X).CommShift ℤ := inferInstance

/-- Derived `ε^*` is a triangulated functor. -/
instance etaleFppfInverseImageDerived.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerived X).IsTriangulated := inferInstance

/-- Derived `ε^*` sends étale `LQCoh^{fbc}` cohomology into fppf
`LQCoh^{fbc}` cohomology. -/
theorem etaleFppfInverseImageDerived_maps_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedCategory.cohomologyIn (lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (etaleFppfInverseImageDerived X) := sorry

/-- Derived inverse image restricted to locally quasi-coherent flat-base-change cohomology. -/
abbrev etaleFppfInverseImageDerivedLQCohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbcEtale X ⥤ DerivedLQCohFbc X :=
  FullSubcategory.restrict (etaleFppfInverseImageDerived X)
    (etaleFppfInverseImageDerived_maps_lqcohFbc X)

/-- Right commuting square of the étale–fppf diagram: restriction to
`D_{LQCoh^{fbc}}` whiskers with the inclusions to unrestricted derived
`ε^*`. -/
abbrev etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleFppfInverseImageDerivedLQCohFbc X ⋙ DerivedLQCohFbc.inclusion X ≅
      DerivedLQCohFbcEtale.inclusion X ⋙ etaleFppfInverseImageDerived X :=
  FullSubcategory.restrict.compιIso (etaleFppfInverseImageDerived X)
    (etaleFppfInverseImageDerived_maps_lqcohFbc X)

/-- Restricted derived `ε^*` on `LQCoh^{fbc}` commutes with shifts. -/
instance etaleFppfInverseImageDerivedLQCohFbc.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedLQCohFbc X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion X) ℤ

/-- Restricted derived `ε^*` on `LQCoh^{fbc}` is triangulated. -/
instance etaleFppfInverseImageDerivedLQCohFbc.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedLQCohFbc X).IsTriangulated := sorry

/-- Derived inverse image on locally quasi-coherent flat-base-change cohomology is an equivalence. -/
instance etaleFppfInverseImageDerivedLQCohFbc.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedLQCohFbc X).IsEquivalence := sorry

/-- Restricted derived `ε^*` sends étale parasitic `LQCoh^{fbc}` objects to
fppf parasitic `LQCoh^{fbc}` objects. -/
theorem etaleFppfInverseImageDerivedLQCohFbc_maps_parasitic
    (X : GroupoidsOver S) [AlgebraicStack X] :
    derivedParasiticEtale X ≤
      (derivedParasitic X).inverseImage
        (etaleFppfInverseImageDerivedLQCohFbc X) := sorry

/-- Objects of étale `D_{LQCoh^{fbc}}` with parasitic cohomology form a
triangulated subcategory. -/
instance derivedParasiticEtale_isTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticEtale X).IsTriangulated := by
  dsimp [derivedParasiticEtale]
  infer_instance

/-- Derived inverse image restricted to parasitic locally quasi-coherent flat-base-change cohomology. -/
abbrev etaleFppfInverseImageDerivedParasitic (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticEtale X).FullSubcategory ⥤
      (derivedParasitic X).FullSubcategory :=
  FullSubcategory.restrict (etaleFppfInverseImageDerivedLQCohFbc X)
    (etaleFppfInverseImageDerivedLQCohFbc_maps_parasitic X)

/-- Left commuting square of the étale–fppf diagram: restriction to parasitic
objects whiskers with the inclusions into `D_{LQCoh^{fbc}}`. -/
abbrev etaleFppfInverseImageDerivedParasitic_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleFppfInverseImageDerivedParasitic X ⋙ (derivedParasitic X).ι ≅
      (derivedParasiticEtale X).ι ⋙ etaleFppfInverseImageDerivedLQCohFbc X :=
  FullSubcategory.restrict.compιIso (etaleFppfInverseImageDerivedLQCohFbc X)
    (etaleFppfInverseImageDerivedLQCohFbc_maps_parasitic X)

/-- Restricted derived `ε^*` on parasitic objects commutes with shifts. -/
instance etaleFppfInverseImageDerivedParasitic.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedParasitic X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (etaleFppfInverseImageDerivedParasitic_comp_inclusion X) ℤ

/-- Restricted derived `ε^*` on parasitic objects is triangulated. -/
instance etaleFppfInverseImageDerivedParasitic.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedParasitic X).IsTriangulated := sorry

/-- Derived inverse image on parasitic locally quasi-coherent flat-base-change cohomology is an equivalence. -/
instance etaleFppfInverseImageDerivedParasitic.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedParasitic X).IsEquivalence := sorry

/-- The canonical functor from étale `D_{LQCoh^{fbc}}` to the étale Verdier
quotient. -/
abbrev DerivedQCohEtale.quotientFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbcEtale X ⥤ DerivedQCohEtale X :=
  verdierQuotientFunctor (derivedParasiticEtale X)

/-- Composite of étale–fppf derived `LQCoh^{fbc}` inverse image with the fppf
Verdier quotient functor. -/
abbrev etaleFppfInverseImageDerivedLQCohFbcToQCoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbcEtale X ⥤ DerivedQCoh X :=
  etaleFppfInverseImageDerivedLQCohFbc X ⋙ DerivedQCoh.quotientFunctor X

/-- The composite through `D_QCoh` inverts the étale parasitic Verdier system. -/
theorem etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.IsInvertedBy
      (etaleFppfInverseImageDerivedLQCohFbcToQCoh X) := sorry

/-- Induced functor on Verdier quotients
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X) / D_{P_X}(X_étale, 𝒪_X) ⥤ D_QCoh(𝒪_X)`. -/
abbrev etaleFppfInverseImageDerivedQCoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohEtale X ⥤ DerivedQCoh X :=
  VerdierQuotient.Exact.factor (derivedParasiticEtale X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X)

/-- Canonical comparison from the étale quotient functor followed by induced
`ε^*` to the composite through fppf `D_QCoh`. -/
abbrev etaleFppfInverseImageDerivedQCoh_facIso (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.Q ⋙ etaleFppfInverseImageDerivedQCoh X ≅
      etaleFppfInverseImageDerivedLQCohFbcToQCoh X :=
  VerdierQuotient.Exact.factor.facIso (derivedParasiticEtale X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X)

/-- The induced quotient functor strictly factors the composite through
`DerivedQCoh.quotientFunctor`. -/
theorem etaleFppfInverseImageDerivedQCoh_fac (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.Q ⋙ etaleFppfInverseImageDerivedQCoh X =
      etaleFppfInverseImageDerivedLQCohFbcToQCoh X :=
  VerdierQuotient.Exact.factor.fac (derivedParasiticEtale X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X)

/-- Induced `ε^*` on Verdier quotients commutes with shifts. -/
instance etaleFppfInverseImageDerivedQCoh.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedQCoh X).CommShift ℤ :=
  VerdierQuotient.Exact.factor.commShift (derivedParasiticEtale X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X)

/-- Induced `ε^*` on Verdier quotients is triangulated. -/
instance etaleFppfInverseImageDerivedQCoh.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedQCoh X).IsTriangulated :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasiticEtale X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
    (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X)

/-- The induced functor of Verdier quotients is an equivalence of triangulated
categories. -/
instance etaleFppfInverseImageDerivedQCoh.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (etaleFppfInverseImageDerivedQCoh X).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
