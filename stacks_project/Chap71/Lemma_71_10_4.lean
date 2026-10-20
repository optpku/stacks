/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.FiniteComponents

/-!
# Lemma 71.10.4

If every weakly associated point of an algebraic space `X` has codimension `0` and `X`
satisfies Morphisms of Spaces Lemma 67.49.1, then `𝒦_X` is a quasi-coherent sheaf of
`𝒪_X`-algebras, affine étale sections of `𝒦_X` are the total ring of fractions of the
corresponding sections of `𝒪_X`, and at a geometric point the stalk of `𝒮_X` (resp. `𝒦_X`)
is the set of nonzerodivisors (resp. the total ring of fractions) of `𝒪_{X, x̄}`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.10.4: The meromorphic-function algebra is quasi-coherent, and its affine étale
sections and geometric stalks are total quotient rings, with denominator stalks equal to the
nonzerodivisors, under the weak-association and finite-component hypotheses. -/
@[stacks 0EN6] #check (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionSheaf_isQuasicoherent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X),
    ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionSheaf_isLocalization_of_isAffine :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (U : affineEtaleSite X),
    IsLocalization (nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))
      ((meromorphicFunctionSheaf X).obj.obj (op U.obj)))

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicDenominatorStalk_eq_nonZeroDivisors :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X),
    meromorphicDenominatorStalk xbar = nonZeroDivisors (structureSheafLiftStalk xbar))

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionStalk_isLocalization :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X),
    IsLocalization (nonZeroDivisors (structureSheafLiftStalk xbar))
      (meromorphicFunctionStalk xbar))

end AlgebraicGeometry.AlgebraicSpace
