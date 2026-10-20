/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction

/-!
# Meromorphic functions on affine schemes

This file relates the total quotient rings of principal localizations of a ring to the canonical
map from the structure sheaf of its spectrum to the meromorphic-function sheaf.
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Spec.MeromorphicFunction

/-- If every non-zero-divisor in every principal localization of a commutative ring is a unit,
then the canonical map from the structure sheaf of its spectrum to the meromorphic-function
sheaf is an isomorphism. -/
theorem toSheafHom_isIso_of_isUnit
    (R : Type u) [CommRing R]
    (h : ∀ (f : R) (z : Localization.Away f),
      z ∈ nonZeroDivisors (Localization.Away f) → IsUnit z) :
    IsIso (LocallyRingedSpace.toMeromorphicFunctionSheafHom
      (Scheme.Spec.obj (Opposite.op <| CommRingCat.of R)).toLocallyRingedSpace) := sorry

end AlgebraicGeometry.Spec.MeromorphicFunction
