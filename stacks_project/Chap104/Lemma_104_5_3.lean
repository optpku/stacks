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
# Lemma 104.5.3

For an algebraic stack `X`, with `P_X` the parasitic objects of
`LQCoh^{fbc}(𝒪_X)`, inverse image `g^* = g⁻¹` along the lisse-étale
(resp. flat-fppf) morphism of Lemma 103.14.2 sends `D_{LQCoh^{fbc}}` of the
large site into `D_QCoh` of the small site, vanishes iff the complex lies in
`D_{P_X}`, and is quasi-inverse to `Lg_!` after passage to the Verdier
quotient `D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 104.5.3 (1): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `g^*` sends `D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)` into
`D_QCoh(𝒪_{X_lisse,étale})`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInverseImageDerived_maps_qcoh :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).inverseImage
        (lisseEtaleModuleInverseImage.derived X))

/- Lemma 104.5.3 (2): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `g^*` of an object of `D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)` vanishes
iff the object lies in `D_{P_X}(X_étale, 𝒪_X)`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInverseImageDerived_isZero_iff_derivedParasitic :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbcEtale X),
    IsZero ((lisseEtaleModuleInverseImage.derived X).obj
        ((DerivedLQCohFbcEtale.inclusion X).obj F)) ↔
      derivedParasiticEtale X F)

/- Lemma 104.5.3 (3): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `Lg_!` sends `D_QCoh(𝒪_{X_lisse,étale})` into
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriekDerived_maps_lqcohFbc :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (lqcohFbc X)).inverseImage
        (lisseEtaleModuleLowerShriek.derived X))

/- Lemma 104.5.3 (4): the induced functors `g^*` and `Lg_!` are mutually
inverse between `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_{X_lisse,étale})`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleDerivedQCohInverseImage.instIsEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (lisseEtaleDerivedQCohInverseImage X).IsEquivalence)

/- Lemma 104.5.3 (5): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `g^*` sends `D_{LQCoh^{fbc}}(𝒪_X)` into
`D_QCoh(𝒪_{X_flat,fppf})`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfInverseImageDerived_maps_qcoh :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).inverseImage
        (flatFppfModuleInverseImage.derived X))

/- Lemma 104.5.3 (6): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `g^*` of an object of `D_{LQCoh^{fbc}}(𝒪_X)` vanishes iff the object
lies in `D_{P_X}(𝒪_X)`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfInverseImageDerived_isZero_iff_derivedParasitic :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbc X),
    IsZero ((flatFppfModuleInverseImage.derived X).obj
        ((DerivedLQCohFbc.inclusion X).obj F)) ↔
      derivedParasitic X F)

/- Lemma 104.5.3 (7): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `Lg_!` sends `D_QCoh(𝒪_{X_flat,fppf})` into
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriekDerived_maps_lqcohFbc :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (flatFppfModuleLowerShriek.derived X))

/- Lemma 104.5.3 (8): the induced functors `g^*` and `Lg_!` are mutually
inverse between `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_{X_flat,fppf})`. -/
@[stacks 07B9]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfDerivedQCohInverseImage.instIsEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (flatFppfDerivedQCohInverseImage X).IsEquivalence)

end AlgebraicGeometry.AlgebraicStack
