/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/- Lemma 31.24.2 (1), denominator clause: at every point of a locally Noetherian scheme, the
local meromorphic denominators are exactly the non-zero-divisors of the local ring. -/
@[stacks 02OV] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian.denominatorStalk_eq_nonZeroDivisors :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] (x : X),
      AlgebraicGeometry.meromorphicDenominatorStalk X x =
        nonZeroDivisors (X.presheaf.stalk x))

/- Lemma 31.24.2 (1), stalk clause: at every point of a locally Noetherian scheme, the
meromorphic-function stalk is the total quotient ring of the local ring. -/
@[stacks 02OV] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian.stalk_isLocalization :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] (x : X),
      IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x))

/- Lemma 31.24.2 (2): on every affine open of a locally Noetherian scheme, meromorphic
sections form the total quotient ring of regular sections. -/
@[stacks 02OV] #check
  (AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian.sections_isLocalization_of_isAffineOpen :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
      (U : X.Opens), AlgebraicGeometry.IsAffineOpen U →
        IsLocalization (nonZeroDivisors Γ(X, U))
          (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)))
