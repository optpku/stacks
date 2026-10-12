/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphisms detected on a submodule quotient

@stack 0H7M

This leaf records the two elementary endomorphism criteria used by quotient-gluing arguments.  The
submodule is arbitrary; ideal multiples and other concrete presentations belong to their own
specialized leaves.
-/

@[expose] public section

universe u v

namespace LinearMap

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An endomorphism that is the identity on a submodule and on the corresponding quotient is
bijective. -/
@[stacks 0H7M "endomorphism identity on a submodule and quotient"]
theorem bijective_of_id_on_submodule_quotient
    (a : M →ₗ[R] M) (N : Submodule R M)
    (hN : ∀ x ∈ N, a x = x)
    (hQ : ∀ x : M, (Submodule.mkQ N) (a x) = (Submodule.mkQ N) x) :
    Function.Bijective a := sorry

/-- If two submodules meet trivially, an endomorphism that is the identity modulo the second one
fixes the first one pointwise. -/
@[stacks 0H7M "endomorphism fixed points from a quotient identity"]
theorem eq_on_of_id_on_quotient
    (N K : Submodule R M) (hNK : N ⊓ K = ⊥) (a : M →ₗ[R] M)
    (hQ : ∀ x : M, (Submodule.mkQ K) (a x) = (Submodule.mkQ K) x) :
    ∀ x ∈ N, a x = x := sorry

end LinearMap
