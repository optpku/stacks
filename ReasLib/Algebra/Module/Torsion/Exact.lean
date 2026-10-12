/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Exact.Sequence
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion-free modules in exact sequences

The middle term of a left-exact pair is torsion-free when both end terms are torsion-free.
-/

@[expose] public section

universe u v w x

namespace Module.IsTorsionFree

variable {R : Type u} [Ring R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup M''] [Module R M'']

/-- If the first map of an exact pair is injective and the two end modules are torsion-free,
then the middle module is torsion-free. -/
@[stacks 0AUS "torsion-free middle term of a left-exact pair"]
theorem of_exact_of_injective {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    [IsTorsionFree R M] [IsTorsionFree R M''] :
    IsTorsionFree R M' := sorry
-- Proof strategy: for each regular scalar, apply `isSMulRegular_of_range_eq_ker` to `hf` and
-- `Function.Exact.linearMap_ker_eq hfg`, using scalar regularity on the two end modules.

end Module.IsTorsionFree
