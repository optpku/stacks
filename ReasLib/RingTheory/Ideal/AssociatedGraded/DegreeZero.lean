/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Internal
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Degree Zero of an Associated Graded Ring

The degree-zero component of `gr_I(R)` is canonically `R ⧸ I`.  This file
uses Mathlib's standard `SetLike.GradeZero` ring and algebra structures and
only supplies the quotient comparison API.

@stack 00K8
-/

@[expose] public section

noncomputable section

universe u

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- The canonical algebra map from `R` onto the degree-zero homogeneous
component of `gr_I(R)` is surjective. -/
theorem gradeZeroAlgebraMap_surjective (I : Ideal R) :
    Function.Surjective (Algebra.ofId R (grade I 0)) := sorry

/-- The kernel of the canonical algebra map to the degree-zero homogeneous
component is exactly `I`. -/
theorem gradeZeroAlgebraMap_ker (I : Ideal R) :
    RingHom.ker (Algebra.ofId R (grade I 0)).toRingHom = I := sorry

/-- The degree-zero homogeneous component of `gr_I(R)` is canonically the
quotient algebra `R ⧸ I`. -/
@[stacks 00K8 "degree-zero associated graded quotient"]
noncomputable def gradeZeroEquivQuotient (I : Ideal R) :
    (R ⧸ I) ≃ₐ[R] grade I 0 :=
  (Ideal.quotientEquivAlgOfEq R (gradeZeroAlgebraMap_ker I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R (grade I 0)) (gradeZeroAlgebraMap_surjective I))

/-- The inverse degree-zero comparison supplies the canonical algebra
structure of `R ⧸ I` over `(gr_I(R))₀`. -/
@[stacks 00K8 "degree-zero scalars on the quotient"]
noncomputable instance gradeZeroAlgebraQuotient (I : Ideal R) :
    @Algebra (grade I 0) (R ⧸ I)
      (SetLike.GradeZero.instCommSemiring (grade I))
      (Ideal.Quotient.semiring I) :=
  let ψ : grade I 0 →+* R ⧸ I :=
    (gradeZeroEquivQuotient I).symm.toRingEquiv.toRingHom
  @RingHom.toAlgebra' (grade I 0) (R ⧸ I)
    (SetLike.GradeZero.instCommSemiring (grade I))
    (Ideal.Quotient.semiring I) ψ
    (fun a b ↦
      @mul_comm (R ⧸ I)
        (Ideal.Quotient.commSemiring I).toCommMonoid.toCommMagma (ψ a) b)

/-- The canonical algebra map `(gr_I(R))₀ → R ⧸ I` is the inverse
degree-zero comparison. -/
@[simp]
theorem gradeZero_algebraMap_quotient (I : Ideal R) (x : grade I 0) :
    @algebraMap (grade I 0) (R ⧸ I)
        (SetLike.GradeZero.instCommSemiring (grade I))
        (Ideal.Quotient.semiring I) (gradeZeroAlgebraQuotient I) x =
      (gradeZeroEquivQuotient I).symm x := sorry

/-- The canonical algebra map `(gr_I(R))₀ → R ⧸ I` is surjective. -/
theorem gradeZero_algebraMap_quotient_surjective (I : Ideal R) :
    Function.Surjective
      (@algebraMap (grade I 0) (R ⧸ I)
        (SetLike.GradeZero.instCommSemiring (grade I))
        (Ideal.Quotient.semiring I) (gradeZeroAlgebraQuotient I)) := sorry

end Ideal.AssociatedGraded

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- The associated graded ring has a canonical algebra structure over its
degree-zero quotient. -/
@[stacks 00K8 "quotient scalars on an associated graded ring", reducible]
noncomputable instance quotientAlgebra (I : Ideal R) :
    Algebra (R ⧸ I) (ring I) :=
  let φ : R ⧸ I →+* ring I :=
    (Ideal.Quotient.liftₐ I (Algebra.ofId R (ring I))
      (by
        intro r hr
        change
          Ideal.Quotient.mk (definingIdeal I)
              (algebraMap R (reesAlgebra I) r) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) hr))).toRingHom
  @RingHom.toAlgebra' (R ⧸ I) (ring I)
    (Quotient.commSemiring I) (Quotient.semiring (definingIdeal I)) φ
    (fun a b ↦
      @mul_comm (ring I)
        (Quotient.commSemiring (definingIdeal I)).toCommMonoid.toCommMagma (φ a) b)

/-- The quotient algebra map sends the class of `r` to the original
coefficient class of `r` in the associated graded ring. -/
@[stacks 00K8 "associated graded quotient scalar map", simp]
theorem quotientAlgebraMap_mk (I : Ideal R) (r : R) :
    algebraMap (R ⧸ I) (ring I) (Ideal.Quotient.mk I r) =
      algebraMap R (ring I) r := by
  change
    Ideal.Quotient.lift I (algebraMap R (ring I)) _
        (Ideal.Quotient.mk I r) = algebraMap R (ring I) r
  exact Ideal.Quotient.lift_mk I (algebraMap R (ring I)) _

/-- The original `R`-action on the associated graded ring factors through
the canonical quotient action by `R ⧸ I`. -/
@[stacks 00K8 "associated graded quotient scalar tower"]
noncomputable instance quotientIsScalarTower (I : Ideal R) :
    IsScalarTower R (R ⧸ I) (ring I) :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext r
    simp [Ideal.Quotient.algebraMap_eq, quotientAlgebraMap_mk]

/-- For a local ring, the associated graded ring of the maximal ideal carries
its canonical quotient action under the standard residue-field name. -/
@[stacks 00K8 "residue-field scalars on a local associated graded ring"]
noncomputable instance residueFieldAlgebra [IsLocalRing R] :
    Algebra (IsLocalRing.ResidueField R)
      (ring (IsLocalRing.maximalIdeal R)) :=
  quotientAlgebra (IsLocalRing.maximalIdeal R)

/-- The residue-field action on the associated graded ring factors the
original action of the local ring. -/
@[stacks 00K8 "local associated graded residue-field scalar tower"]
noncomputable instance residueFieldIsScalarTower [IsLocalRing R] :
    IsScalarTower R (IsLocalRing.ResidueField R)
      (ring (IsLocalRing.maximalIdeal R)) :=
  quotientIsScalarTower (IsLocalRing.maximalIdeal R)

end Ideal.AssociatedGraded
