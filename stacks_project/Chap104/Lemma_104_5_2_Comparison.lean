/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact
public import stacks_project.Chap103.Proposition_103_8_1
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Étale–fppf inverse image on derived quasi-coherent modules

Identity-on-objects comparison `ε : X_fppf ⟶ X_étale` gives exact inverse
image `ε^*` on module sheaves. Restricting to `D_{LQCoh^{fbc}}` and to the
parasitic subcategory, then factoring through the Verdier quotient, produces
the comparison functors from the étale derived categories into `D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Underived inverse image `ε^*` of module sheaves along `etaleFppfHom`. -/
abbrev etaleFppfInverseImage (X : GroupoidsOver S) :
    etaleModules X ⥤ fppfModules X :=
  (etaleFppfHom X).modulePullback.{u}

/-- `etaleFppfInverseImage` is module pullback along `etaleFppfHom`. -/
theorem etaleFppfInverseImage_eq (X : GroupoidsOver S) :
    etaleFppfInverseImage X = (etaleFppfHom X).modulePullback.{u} := sorry

/-- The identity-on-objects comparison `ε : X_fppf ⟶ X_étale` is categorically
flat, so `ε^*` is exact on module sheaves. -/
instance etaleFppfHom_isFlat (X : GroupoidsOver S) [AlgebraicStack X] :
    IsFlat.{u} (etaleFppfHom X) := sorry

/-- Underived `ε^*` is additive. -/
instance etaleFppfInverseImage.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (etaleFppfInverseImage X).Additive :=
  modulePullback_additive (etaleFppfHom X)

/-- Bundled exact underived inverse image along `etaleFppfHom`. -/
abbrev etaleFppfInverseImageExact (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleModules X ⥤ₑ fppfModules X :=
  IsFlat.exactPullback.{u} (etaleFppfHom X)

/-- `etaleFppfInverseImageExact` is the exact pullback of `etaleFppfHom`. -/
theorem etaleFppfInverseImageExact_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    etaleFppfInverseImageExact X = IsFlat.exactPullback.{u} (etaleFppfHom X) :=
  sorry

/-- Derived inverse image `ε^* : D(X_étale, 𝒪_X) ⥤ D(𝒪_X)`. -/
abbrev etaleFppfInverseImageDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerivedEtale X ⥤ ModuleDerived X :=
  ExactFunctor.mapDerivedCategory (etaleFppfInverseImageExact X)

/-- Derived `ε^*` is `mapDerivedCategory` of the exact pullback of
`etaleFppfHom`. -/
theorem etaleFppfInverseImageDerived_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    etaleFppfInverseImageDerived X =
      ExactFunctor.mapDerivedCategory (etaleFppfInverseImageExact X) := sorry

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

/-- Middle vertical arrow: derived `ε^*` on `D_{LQCoh^{fbc}}`. -/
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

/-- The right square is the inclusion comparison of the restricted derived
`ε^*`. -/
theorem etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion_eq
    (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion X =
      FullSubcategory.restrict.compιIso (etaleFppfInverseImageDerived X)
        (etaleFppfInverseImageDerived_maps_lqcohFbc X) := sorry

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

/-- The middle vertical arrow is an equivalence of triangulated categories. -/
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
    (derivedParasiticEtale X).IsTriangulated := sorry

/-- Left vertical arrow: derived `ε^*` on `D_{P_X}`. -/
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

/-- The left square is the inclusion comparison of the parasitic restriction. -/
theorem etaleFppfInverseImageDerivedParasitic_comp_inclusion_eq
    (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleFppfInverseImageDerivedParasitic_comp_inclusion X =
      FullSubcategory.restrict.compιIso (etaleFppfInverseImageDerivedLQCohFbc X)
        (etaleFppfInverseImageDerivedLQCohFbc_maps_parasitic X) := sorry

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

/-- The left vertical arrow is an equivalence of triangulated categories. -/
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

/-- `etaleFppfInverseImageDerivedQCoh` is the canonical exact Verdier factor of
the composite through `DerivedQCoh.quotientFunctor`. -/
theorem etaleFppfInverseImageDerivedQCoh_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    etaleFppfInverseImageDerivedQCoh X =
      VerdierQuotient.Exact.factor (derivedParasiticEtale X)
        (etaleFppfInverseImageDerivedLQCohFbcToQCoh X)
        (etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts X) := sorry

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
      etaleFppfInverseImageDerivedLQCohFbcToQCoh X := sorry

/-- The étale cohomology-in subcategory is triangulated. -/
instance derivedLQCohFbcEtale_isTriangulatedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsTriangulated (DerivedLQCohFbcEtale X) := inferInstance

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
