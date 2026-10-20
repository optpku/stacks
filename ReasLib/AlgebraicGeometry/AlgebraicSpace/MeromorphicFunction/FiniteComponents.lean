/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Stalk

/-!
# Meromorphic functions with locally finite irreducible components

When weakly associated points have codimension zero and compact opens have finitely many
irreducible components, the meromorphic-function algebra is quasi-coherent. Its affine étale
sections and geometric stalks are total quotient rings of the corresponding structure rings.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If weakly associated points have codimension zero and compact opens have finitely many
irreducible components, the meromorphic-function algebra is quasi-coherent over the
structure sheaf. -/
@[stacks 0EN6]
theorem meromorphicFunctionSheaf_isQuasicoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) :
    ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).IsQuasicoherent :=
  sorry

/-- If weakly associated points have codimension zero and compact opens have finitely many
irreducible components, meromorphic functions on every affine étale chart form the total
quotient ring of its structure-sheaf sections. -/
@[stacks 0EN6]
theorem meromorphicFunctionSheaf_isLocalization_of_isAffine {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (U : affineEtaleSite X) :
    IsLocalization (nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))
      ((meromorphicFunctionSheaf X).obj.obj (op U.obj)) :=
  sorry

/-- If weakly associated points have codimension zero and compact opens have finitely many
irreducible components, the denominator stalk at each geometric point consists exactly of
the nonzerodivisors of the structure stalk. -/
@[stacks 0EN6]
theorem meromorphicDenominatorStalk_eq_nonZeroDivisors {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X) :
    meromorphicDenominatorStalk xbar = nonZeroDivisors (structureSheafLiftStalk xbar) :=
  sorry

/-- If weakly associated points have codimension zero and compact opens have finitely many
irreducible components, the meromorphic-function stalk at each geometric point is the total
quotient ring of the structure stalk. -/
@[stacks 0EN6]
theorem meromorphicFunctionStalk_isLocalization {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X) :
    IsLocalization (nonZeroDivisors (structureSheafLiftStalk xbar))
      (meromorphicFunctionStalk xbar) :=
  sorry

/-- Under the weak-association and finite-component hypotheses, the meromorphic-function
algebra has its canonical quasi-coherent underlying module. -/
instance instIsQuasicoherentMeromorphicFunctionSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [Fact (X.weakAss ⊆ codimZeroPoints X)] :
    ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).IsQuasicoherent :=
  meromorphicFunctionSheaf_isQuasicoherent X Fact.out

/-- Under the weak-association and finite-component hypotheses, the canonical algebra on
meromorphic sections of an affine étale chart is a localization at the nonzerodivisors. -/
instance instIsLocalizationMeromorphicFunctionSheafOfIsAffine {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [Fact (X.weakAss ⊆ codimZeroPoints X)] (U : affineEtaleSite X) :
    IsLocalization (nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))
      ((meromorphicFunctionSheaf X).obj.obj (op U.obj)) :=
  meromorphicFunctionSheaf_isLocalization_of_isAffine Fact.out U

/-- Under the weak-association and finite-component hypotheses, the canonical meromorphic
stalk algebra at a geometric point is a localization at the structure stalk's nonzerodivisors. -/
instance instIsLocalizationMeromorphicFunctionStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [Fact (X.weakAss ⊆ codimZeroPoints X)] (xbar : GeometricPoint X) :
    IsLocalization (nonZeroDivisors (structureSheafLiftStalk xbar))
      (meromorphicFunctionStalk xbar) :=
  meromorphicFunctionStalk_isLocalization Fact.out xbar

end AlgebraicGeometry.AlgebraicSpace
