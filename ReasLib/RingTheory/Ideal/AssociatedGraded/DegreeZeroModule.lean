/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.DegreeZero
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module

/-!
# Degree-Zero Scalars on an Associated Graded Module

The equivalence `(R ⧸ I) ≃ (gr_I(R))₀` canonically restricts the scalar
action on `gr_I(M)`.  This file owns that instance once, so downstream Hilbert
function arguments do not rebuild local `Module`, `SMul`, or scalar-tower
instances.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The degree-zero component acts on `gr_I(M)` through its canonical
identification with `R ⧸ I`. -/
@[stacks 00K8 "degree-zero action on an associated graded module"]
noncomputable instance moduleGradeZero (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
  Module (grade I 0) (gradedModule I M) :=
  @Module.compHom (R ⧸ I) (grade I 0) (gradedModule I M)
    inferInstance inferInstance inferInstance CommSemiring.toSemiring
    (gradeZeroEquivQuotient I).symm.toRingEquiv.toRingHom

/-- The degree-zero action factors through the quotient-ring action on the
associated graded module. -/
noncomputable instance scalarTowerGradeZeroQuotient
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    @IsScalarTower (grade I 0) (R ⧸ I) (gradedModule I M)
      (@Algebra.toSMul (grade I 0) (R ⧸ I)
        (SetLike.GradeZero.instCommSemiring (grade I))
        (Ideal.Quotient.semiring I) (gradeZeroAlgebraQuotient I))
      (inferInstance : SMul (R ⧸ I) (gradedModule I M))
      (@SMul.comp (R ⧸ I) (grade I 0) (gradedModule I M)
        (inferInstance : SMul (R ⧸ I) (gradedModule I M))
        ((gradeZeroEquivQuotient I).symm.toRingEquiv.toRingHom)) := sorry

/-- The integer grading of `gr_I(M)`, regarded as submodules over its
degree-zero coefficient ring. -/
@[stacks 00K8 "degree-zero associated graded components"]
def gradeZeroIntGrade (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    ℤ → Submodule (grade I 0) (gradedModule I M) :=
  fun n ↦ Submodule.restrictScalars (grade I 0) (intGrade I M n)

/-- Restricting an integer-graded component to degree-zero scalars does not
change its underlying carrier. -/
@[simp]
theorem mem_gradeZeroIntGrade (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℤ) (x : gradedModule I M) :
    x ∈ gradeZeroIntGrade I M n ↔ x ∈ intGrade I M n := sorry

end Ideal.AssociatedGraded
