/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Product
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Kunneth

/-!
# Cohomology of twists on a product of projective lines

This file records the closed-form cohomology dimensions of external tensor-product
twists on the product of two projective lines over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.Product

/-- The closed-form cohomology dimension of a twist on the product of two projective lines. -/
def twistingSheafCohomologyFinrank (a b : ℤ) (i : ℕ) : ℕ :=
  match i with
  | 0 => (a + 1).toNat * (b + 1).toNat
  | 1 => (a + 1).toNat * (-b - 1).toNat + (-a - 1).toNat * (b + 1).toNat
  | 2 => (-a - 1).toNat * (-b - 1).toNat
  | _ => 0

/-- The degree-zero branch of the cohomology dimension formula. -/
theorem twistingSheafCohomologyFinrank_zero (a b : ℤ) :
    twistingSheafCohomologyFinrank a b 0 = (a + 1).toNat * (b + 1).toNat := sorry

/-- The degree-one branch of the cohomology dimension formula. -/
theorem twistingSheafCohomologyFinrank_one (a b : ℤ) :
    twistingSheafCohomologyFinrank a b 1 =
      (a + 1).toNat * (-b - 1).toNat + (-a - 1).toNat * (b + 1).toNat := sorry

/-- The degree-two branch of the cohomology dimension formula. -/
theorem twistingSheafCohomologyFinrank_two (a b : ℤ) :
    twistingSheafCohomologyFinrank a b 2 = (-a - 1).toNat * (-b - 1).toNat := sorry

/-- The cohomology dimension formula vanishes in every degree greater than `2`. -/
theorem twistingSheafCohomologyFinrank_of_two_lt (a b : ℤ) {i : ℕ} (hi : 2 < i) :
    twistingSheafCohomologyFinrank a b i = 0 := sorry

/-- Cohomology of an external tensor-product twist on the product is finite-dimensional over `k`. -/
instance finiteDimensional_cohomology_twistingSheaf
    (k : Type u) [Field k] (a b : ℤ) (i : ℕ) :
    FiniteDimensional k (Scheme.Hom.cohomology (toSpec k) (twistingSheaf k a b) i) := sorry

/-- The cohomology finrank of an external tensor-product twist is given by the closed formula. -/
theorem cohomologyFinrank_twistingSheaf
    (k : Type u) [Field k] (a b : ℤ) (i : ℕ) :
    Scheme.Hom.cohomologyFinrank (toSpec k) (twistingSheaf k a b) i =
      twistingSheafCohomologyFinrank a b i := sorry

end AlgebraicGeometry.ProjectiveLine.Product
