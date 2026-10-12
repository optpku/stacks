/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.CrossRefAttribute

/-!
# Duals of cokernels of injective finite-free endomorphisms

An injective endomorphism of a finite free module has cokernel with zero linear dual.  The
annihilator statement is the reusable core, while the final theorem records the standard
`Fin n → R` presentation from the source.

@stack 0EWY
-/

@[expose] public section

universe u v

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The dual annihilator of the range of an injective endomorphism of a finite free module is
bottom. -/
@[stacks 0EWY "dual annihilator of an injective finite-free endomorphism"]
theorem range_dualAnnihilator_eq_bot_of_injective
    (phi : M →ₗ[R] M) (hphi : Function.Injective phi) :
    (LinearMap.range phi).dualAnnihilator = ⊥ := sorry
-- Proof strategy: choose a finite basis of the free module and use the determinant/adjugate
-- description of the dual endomorphism to show that every functional vanishing on `range phi`
-- is zero; conclude the submodule equality by extensionality.

/-- The linear dual of the cokernel of an injective endomorphism of a finite free module is a
subsingleton. -/
@[stacks 0EWY "dual of the cokernel of an injective finite-free endomorphism"]
theorem quotient_range_dual_subsingleton_of_injective
    (phi : M →ₗ[R] M) (hphi : Function.Injective phi) :
    Subsingleton (Module.Dual R (M ⧸ LinearMap.range phi)) := sorry
-- Proof strategy: precompose a quotient functional with `Submodule.mkQ`; its kernel contains
-- `range phi`, so it lies in `range phi`'s dual annihilator.  Apply
-- `range_dualAnnihilator_eq_bot_of_injective` and quotient induction to show the original
-- functional is zero, then use `subsingleton_iff`.

/-- Every linear functional on the cokernel of an injective endomorphism of a finite free module
is zero. -/
@[stacks 0EWY "vanishing dual of an injective finite-free endomorphism cokernel"]
theorem quotient_range_dual_eq_zero_of_injective
    (phi : M →ₗ[R] M) (hphi : Function.Injective phi)
    (f : Module.Dual R (M ⧸ LinearMap.range phi)) :
    f = 0 := sorry
-- Proof strategy: obtain
-- `quotient_range_dual_subsingleton_of_injective phi hphi` and eliminate `f` against the zero
-- functional using the resulting subsingleton equality.

/-- Lemma 15.15.7: if `phi : R^n → R^n` is an injective linear map, then
`Module.Dual R ((Fin n → R) ⧸ LinearMap.range phi)` is zero. -/
@[stacks 0EWY]
theorem quotient_range_dual_eq_zero_of_injective_fin {n : ℕ}
    (phi : (Fin n → R) →ₗ[R] (Fin n → R)) (hphi : Function.Injective phi)
    (f : Module.Dual R ((Fin n → R) ⧸ LinearMap.range phi)) :
    f = 0 := sorry
-- Proof strategy: specialize `quotient_range_dual_eq_zero_of_injective` to the canonical finite
-- free module `Fin n → R`; its standard `Module.Free` and `Module.Finite` instances discharge the
-- structural hypotheses.

end LinearMap
