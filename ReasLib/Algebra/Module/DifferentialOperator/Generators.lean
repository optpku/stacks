module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Operators Checked on Algebra Generators

This leaf isolates the subalgebra argument which promotes commutator bounds
from a generating family to all scalars.  It does not use principal parts.

@stack 0G35
-/

@[expose] public section

universe u v w x y

namespace LinearMap.IsDifferentialOperatorOfOrder

section Generators

variable {R : Type u} {S : Type v} {ι : Type w} {M : Type x} {N : Type y}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module S M] [Module S N] [Module R M] [Module R N]
variable [IsScalarTower R S M] [IsScalarTower R S N]

/-- Lemma 10.133.11, tag 0G35: to prove that `D` has order at most `k + 1`, it is enough to
check its order-`k` scalar commutators on any family generating `S` as an `R`-algebra. -/
@[stacks 0G35]
theorem of_generators (g : ι → S) (hgen : Algebra.adjoin R (Set.range g) = ⊤)
    {D : M →ₗ[R] N} {k : ℕ}
    (hD : ∀ i : ι, (D.scalarCommutator (g i)).IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder S (k + 1) := sorry

end Generators

end LinearMap.IsDifferentialOperatorOfOrder
