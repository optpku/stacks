/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.FiniteComponents

/-!
# Meromorphic functions on locally Noetherian schemes

The local meromorphic denominators on a locally Noetherian scheme are precisely the
non-zero-divisors. Consequently, meromorphic-function stalks and affine sections have the
universal property of total quotient rings.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- At every point of a locally Noetherian scheme, germs of local meromorphic denominators
are exactly the non-zero-divisors of the local ring. -/
theorem denominatorStalk_eq_nonZeroDivisors (x : X) :
    meromorphicDenominatorStalk X x = nonZeroDivisors (X.presheaf.stalk x) := sorry

/-- At every point of a locally Noetherian scheme, the meromorphic-function stalk is a
localization of the local ring at its non-zero-divisors. -/
theorem stalk_isLocalization (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x) := sorry

/-- On an affine open of a locally Noetherian scheme, meromorphic functions form the
localization of regular functions at the non-zero-divisors. -/
theorem sections_isLocalization_of_isAffineOpen
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)) := sorry

end AlgebraicGeometry.Scheme.MeromorphicFunction.Noetherian
