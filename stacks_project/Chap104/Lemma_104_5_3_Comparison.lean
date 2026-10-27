/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.SmallSites
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.SiteComparison
import StacksCheckRecall

/-!
# Derived quasi-coherent site comparisons

The comparison results are provided by the mathematical owners imported above.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Derived module lower shriek from the flat-fppf site to the large fppf site. -/
abbrev derivedFlatFppfLowerShriek {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : ModuleDerivedFlatFppf X ⥤ ModuleDerived X :=
  flatFppfModuleLowerShriek.derived X

/- Lemma 104.5.3: inverse image and lower shriek compare the large-site
parasitic derived quotients with the small-site quasi-coherent categories. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInverseImageDerived_maps_qcoh :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).inverseImage
        (lisseEtaleModuleInverseImage.derived X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInverseImageDerived_isZero_iff_derivedParasitic :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbcEtale X),
    IsZero ((lisseEtaleModuleInverseImage.derived X).obj
        ((DerivedLQCohFbcEtale.inclusion X).obj F)) ↔
      derivedParasiticEtale X F)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriekDerived_maps_lqcohFbc :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (lqcohFbc X)).inverseImage
        (lisseEtaleModuleLowerShriek.derived X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleDerivedQCohInverseImage.instIsEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (lisseEtaleDerivedQCohInverseImage X).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInverseImageDerived_maps_qcoh :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).inverseImage
        (flatFppfModuleInverseImage.derived X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInverseImageDerived_isZero_iff_derivedParasitic :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbc X),
    IsZero ((flatFppfModuleInverseImage.derived X).obj
        ((DerivedLQCohFbc.inclusion X).obj F)) ↔
      derivedParasitic X F)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriekDerived_maps_lqcohFbc :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (flatFppfModuleLowerShriek.derived X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfDerivedQCohInverseImage.instIsEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (flatFppfDerivedQCohInverseImage X).IsEquivalence)

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

#check (CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.fac
    (derivedParasiticEtale X) (lisseEtaleInverseImageDerivedLQCohFbc X)
    (lisseEtaleInverseImageDerivedLQCohFbc_inverts X) :
    (derivedParasiticEtale X).trW.Q ⋙ lisseEtaleDerivedQCohEtaleInverseImage X =
      lisseEtaleInverseImageDerivedLQCohFbc X)

#check (CategoryTheory.ObjectProperty.VerdierQuotient.Exact.factor.fac
    (derivedParasitic X) (flatFppfInverseImageDerivedLQCohFbc X)
    (flatFppfInverseImageDerivedLQCohFbc_inverts X) :
    (derivedParasitic X).trW.Q ⋙ flatFppfDerivedQCohInverseImage X =
      flatFppfInverseImageDerivedLQCohFbc X)

end AlgebraicGeometry.AlgebraicStack
