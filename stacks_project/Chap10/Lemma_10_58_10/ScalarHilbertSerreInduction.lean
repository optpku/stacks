/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.Hilbert
public import ReasLib.Algebra.Module.Graded.Decomposition.SMul
public import ReasLib.LinearAlgebra.Quotient.Map
import StacksCheckRecall

/-!
# Lemma 10.58.10: scalar graded support

@stack 00K3
-/

@[expose] public section

open Filter
open HomogeneousIdeal
open scoped BigOperators DirectSum

-- Local instance justification (search instability): Mathlib intentionally keeps the canonical
-- MvPolynomial graded-algebra instance local to avoid global instance diamonds.
attribute [local instance] MvPolynomial.gradedAlgebra
-- Local instance justification (search instability): the matching decomposition is likewise a
-- canonical but localized MvPolynomial choice in Mathlib.
attribute [local instance] MvPolynomial.decomposition
-- Local instance justification (search instability): enabling the homogeneous scalar monoid only
-- here avoids competing graded-action instances for unrelated polynomial gradings.
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u v

section

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module k M]
variable [Module (MvPolynomial (Fin d) k) M] [IsScalarTower k (MvPolynomial (Fin d) k) M]

-- Local declaration justification (source-local notation): these two canonical objects recur in
-- the homogeneous-kernel bridge and owner recalls below; keeping them local avoids a public
-- vocabulary leak.
local notation "S" => MvPolynomial (Fin d) k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin d) k

/-- Auxiliary support for Lemma 10.58.10: kernels of iterated multiplication by a degree-one scalar
are homogeneous for scalar graded pieces. -/
lemma scalar_degree_one_mul_kernel_pow_isHomogeneous
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha_deg : a ∈ 𝒜 1) (r : ℕ) :
    ((LinearMap.ker ((a • LinearMap.id : M →ₗ[S] M) ^ r)).restrictScalars k).IsHomogeneous ℳ := sorry
/- API design: stabilization is supplied by `LinearMap.eventually_iSup_ker_pow_eq`, while quotient
injectivity is grading-free and owned by `LinearMap.mapQ_ker_pow_injective_of_iSup_eq`.  They stay
separate from the homogeneous-kernel statement above; an existential conjunction package would
hide the chosen stage and duplicate canonical quotient-map data. -/


/- Canonical graded support for the source-facing Lemma 10.58.10 recall. -/
@[stacks 00K3 "degree-one graded scalar projection"]
#check @DirectSum.coe_decompose_smul_vadd_of_left_mem
@[stacks 00K3 "homogeneous kernel of a degree-one scalar"]
#check @scalar_degree_one_mul_kernel_pow_isHomogeneous
@[stacks 00K3 "Noetherian stabilization of power kernels"]
#check @LinearMap.eventually_iSup_ker_pow_eq
@[stacks 00K3 "injectivity on the stabilized power-kernel quotient"]
#check @LinearMap.mapQ_ker_pow_injective_of_iSup_eq
end
