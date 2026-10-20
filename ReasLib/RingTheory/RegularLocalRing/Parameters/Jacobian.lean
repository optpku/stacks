/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobian criterion for partial regular systems of parameters

A unit determinant of absolute derivations makes the chosen maximal-ideal classes linearly
independent in the cotangent space.  The reusable core records the resulting partial regular
system of parameters; the two source-facing consequences retain the positive-length hypothesis.

@stack 0GEE
-/

@[expose] public section

universe u

open RingTheory Sequence

namespace IsLocalRing.IsPartOfRegularSystemOfParameters

/-- A unit Jacobian determinant makes a finite maximal-ideal family part of a regular system of
parameters.  This canonical core also applies to the empty family. -/
@[stacks 0GEE "partial regular-system bridge"]
theorem of_jacobianDet_isUnit
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {m : ℕ}
    (x : Fin m → IsLocalRing.maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsLocalRing.IsPartOfRegularSystemOfParameters
      (IsLocalRing.maximalIdeal R).spanFinrank x := sorry

end IsLocalRing.IsPartOfRegularSystemOfParameters

namespace IsRegularLocalRing

/-- Lemma 15.48.3 (1) (Stacks `0GEE`): for a nonempty finite family with unit Jacobian
determinant, quotienting by its parameter ideal gives a regular local ring. -/
@[stacks 0GEE "regular quotient"]
theorem quotient_parameterIdeal_of_jacobianDet_isUnit
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {m : ℕ}
    (hm : 1 ≤ m) (x : Fin m → IsLocalRing.maximalIdeal R)
    (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegularLocalRing (R ⧸ IsLocalRing.parameterIdeal x) := sorry

/-- Lemma 15.48.3 (2) (Stacks `0GEE`): under the same positive-length and unit-Jacobian
hypotheses, the chosen family is a regular sequence. -/
@[stacks 0GEE "regular sequence"]
theorem sequence_isRegular_of_jacobianDet_isUnit
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {m : ℕ}
    (hm : 1 ≤ m) (x : Fin m → IsLocalRing.maximalIdeal R)
    (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) := sorry

end IsRegularLocalRing
