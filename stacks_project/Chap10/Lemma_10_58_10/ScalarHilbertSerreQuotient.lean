/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_58_10.ScalarHilbertSerre
public import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars

/-!
# Principal scalar quotient support for Lemma 10.58.10

@stack 052N
-/

@[expose] public section

open HomogeneousIdeal

-- Local instance justification (search instability): Mathlib keeps these canonical MvPolynomial
-- grading instances localized to avoid global instance diamonds.
attribute [local instance] MvPolynomial.gradedAlgebra
-- Local instance justification (search instability): the canonical decomposition is enabled only
-- for this quotient-grading calculation.
attribute [local instance] MvPolynomial.decomposition
-- Local instance justification (search instability): the homogeneous scalar monoid is confined to
-- this quotient leaf so unrelated graded actions do not compete during inference.
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u v

section

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module k M]
variable [Module (MvPolynomial (Fin d) k) M] [IsScalarTower k (MvPolynomial (Fin d) k) M]

-- Local declaration justification (source-local notation): the fixed polynomial ring is repeated
-- in the quotient carrier and scalar-action statements below.
local notation "S" => MvPolynomial (Fin d) k

omit [Module k M] [IsScalarTower k S M] in
/-- Helper for Chap10 Lemma 10 58 10: the quotient by `(a)M` is killed by multiplication by
`a`. -/
@[stacks 052N "principal scalar quotient annihilation"]
lemma quotient_smul_eq_zero_of_span_singleton_smul_top
    (a : S) (q : M ⧸ ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M))) :
    a • q = 0 := sorry

end
