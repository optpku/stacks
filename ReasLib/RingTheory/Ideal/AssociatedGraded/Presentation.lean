/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReasLib.RingTheory.Ideal.AssociatedGraded.DegreeZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial Presentations of Associated Graded Rings

A family `x : ι → I` determines the canonical polynomial evaluation map

`(R ⧸ I)[X_i] → gr_I(R)`

sending `X_i` to the degree-one class of `x i`.  This file owns that map
independently of any regularity or quasi-regularity hypothesis; such
hypotheses belong in theorems asserting that the map is bijective.

@stack 00NO
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.AssociatedGraded.Presentation

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- Polynomial evaluation in the degree-one classes of a family in `I`. -/
@[stacks 00NO "associated graded polynomial presentation map"]
noncomputable def map {I : Ideal R} (x : ι → I) :
    MvPolynomial ι (R ⧸ I) →ₐ[R ⧸ I] AssociatedGraded.ring I :=
  MvPolynomial.aeval fun i ↦ AssociatedGraded.degreeOne (x i)

/-- The presentation map sends each variable to its prescribed degree-one
class. -/
@[simp]
theorem map_X {I : Ideal R} (x : ι → I) (i : ι) :
    map x (MvPolynomial.X i) = AssociatedGraded.degreeOne (x i) := by
  simp [map]

/-- The presentation map agrees with the canonical quotient algebra map on
coefficients. -/
@[simp]
theorem map_C {I : Ideal R} (x : ι → I) (r : R ⧸ I) :
    map x (MvPolynomial.C r) =
      algebraMap (R ⧸ I) (AssociatedGraded.ring I) r := by
  simp [map]

/-- A family generating the ideal gives a surjective polynomial presentation of
the associated graded ring. -/
@[stacks 00NO, stacks 063H "associated graded presentation map surjective"]
theorem map_surjective {I : Ideal R} (x : ι → I)
    (hI : I ≤ Ideal.span (Set.range fun i ↦ (x i : R))) :
    Function.Surjective (map x) := sorry

/-- For a generating family, bijectivity of the presentation map reduces to
injectivity. -/
theorem map_bijective_iff_injective {I : Ideal R} (x : ι → I)
    (hI : I ≤ Ideal.span (Set.range fun i ↦ (x i : R))) :
    Function.Bijective (map x) ↔ Function.Injective (map x) :=
  and_iff_left (map_surjective x hI)

end Ideal.AssociatedGraded.Presentation
