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
    Function.Surjective (map x) := by
  let S : Subalgebra R (AssociatedGraded.ring I) :=
    (map x).range.restrictScalars R
  let T : Subalgebra R (Polynomial R) :=
    (S.comap (AssociatedGraded.quotientMap I)).map (reesAlgebra I).val
  have hgen : Ideal.span (Set.range fun i ↦ (x i : R)) ≤
      T.toSubmodule.comap (Polynomial.monomial 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Polynomial.monomial 1 (x i : R) ∈ T
    refine ⟨ReesAlgebra.Grading.degreeOne I (x i), ?_, rfl⟩
    change AssociatedGraded.degreeOne (x i) ∈ (map x).range
    exact ⟨MvPolynomial.X i, map_X x i⟩
  have hrees : reesAlgebra I ≤ T := by
    rw [← adjoin_monomial_eq_reesAlgebra I]
    apply Algebra.adjoin_le
    rintro _ ⟨r, hr, rfl⟩
    exact hgen (hI hr)
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := AssociatedGraded.definingIdeal I) y
  obtain ⟨q, hq, hqp⟩ := hrees p.2
  have hqp' : q = p := Subtype.ext hqp
  subst q
  exact hq

/-- A preimage under the canonical presentation, chosen only from its proved
surjectivity. No injectivity or regularity certificate is used to select this
polynomial. -/
noncomputable def preimage {I : Ideal R} (x : ι → I)
    (hI : I ≤ Ideal.span (Set.range fun i ↦ (x i : R))) :
    AssociatedGraded.ring I → MvPolynomial ι (R ⧸ I) :=
  Function.surjInv (map_surjective x hI)

/-- The selected polynomial evaluates to the given associated-graded element. -/
@[simp]
theorem map_preimage {I : Ideal R} (x : ι → I)
    (hI : I ≤ Ideal.span (Set.range fun i ↦ (x i : R)))
    (y : AssociatedGraded.ring I) :
    map x (preimage x hI y) = y :=
  Function.surjInv_eq (map_surjective x hI) y

/-- For a generating family, bijectivity of the presentation map reduces to
injectivity. -/
theorem map_bijective_iff_injective {I : Ideal R} (x : ι → I)
    (hI : I ≤ Ideal.span (Set.range fun i ↦ (x i : R))) :
    Function.Bijective (map x) ↔ Function.Injective (map x) :=
  and_iff_left (map_surjective x hI)

end Ideal.AssociatedGraded.Presentation
