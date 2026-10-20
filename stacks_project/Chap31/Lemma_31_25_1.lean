/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced
import StacksCheckRecall

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

/- Lemma 31.25.1 (1): the meromorphic-function sheaf is the product of the direct images of the
residue fields at the generic points of the irreducible components. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.sheaf_iso_genericPointResidueFieldPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
        (AlgebraicGeometry.genericPointResidueFieldPushforwardProductSheaf X))

/- Lemma 31.25.1 (2): the meromorphic-function sheaf is bundled as a quasicoherent algebra over
the structure sheaf. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.qcAlgebra :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.QcAlgebraUnder)

/- Lemma 31.25.1 (3): the meromorphic-function algebra is quasicoherent as a module over the
structure sheaf. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.sheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (SheafOfModules.unit
          (ringSheaf (Opens.grothendieckTopology X.toTopCat)
            X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
          ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
            X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent)

/- Lemma 31.25.1 (4): meromorphic sections of a quasicoherent module are the coproduct of the
direct images of the module stalks at the generic points. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced.sheaf_isIsomorphic_genericPointStalkPushforwardCoproduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsIsomorphic
        ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
          (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
        (AlgebraicGeometry.genericPointStalkPushforwardCoproductModule X ℱ))

/- Lemma 31.25.1 (5): meromorphic sections of a quasicoherent module are the product of the
direct images of the module stalks at the generic points. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced.sheaf_isIsomorphic_genericPointStalkPushforwardProduct :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsIsomorphic
        ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
          (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
        (AlgebraicGeometry.genericPointStalkPushforwardProductModule X ℱ))

/- Lemma 31.25.1 (6): meromorphic sections of a quasicoherent module are quasicoherent over the
structure sheaf. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced.sheaf_isQuasicoherent :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent)

/- Lemma 31.25.1 (7): the local meromorphic denominators are exactly the non-zero-divisors in
the local ring. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.denominatorStalk_eq_nonZeroDivisors :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X),
      AlgebraicGeometry.meromorphicDenominatorStalk X x =
        nonZeroDivisors (X.presheaf.stalk x))

/- Lemma 31.25.1 (8): every meromorphic-function stalk is the total quotient ring of the local
ring. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.stalk_isLocalization :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X),
      IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x))

/- Lemma 31.25.1 (9): meromorphic functions on an affine open form the total quotient ring of
its regular functions. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.sections_isLocalization_of_isAffineOpen :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (U : X.Opens), AlgebraicGeometry.IsAffineOpen U →
      IsLocalization (nonZeroDivisors Γ(X, U))
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)))

/- Lemma 31.25.1 (10): the rational-function ring is the ring of global meromorphic
functions. -/
@[stacks 02OW] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced.rationalFunctionRing_iso_meromorphicFunctions :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsIsomorphic X.rationalFunctionRing X.toLocallyRingedSpace.meromorphicFunctions)
