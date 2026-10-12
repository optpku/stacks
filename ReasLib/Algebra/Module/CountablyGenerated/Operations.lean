/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import ReasLib.Algebra.Module.CountablyGenerated.Basic

/-!
# Operations on countably generated modules

This file contains the elementary functorial API for `Module.CountablyGenerated` and
`Module.IsDirectSumOfCountablyGenerated`.  It is independent of projectivity and flatness.
-/

@[expose] public section

universe u v w x

namespace Module.CountablyGenerated

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Every finite module is countably generated. -/
theorem of_finite [Module.Finite R M] : CountablyGenerated R M := sorry

/-- A surjective linear image of a countably generated module is countably generated. -/
theorem map (hM : CountablyGenerated R M) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : CountablyGenerated R N := sorry

/-- Countable generation is preserved by linear equivalence. -/
theorem of_linearEquiv (e : M ≃ₗ[R] N) (hN : CountablyGenerated R N) :
    CountablyGenerated R M := sorry

end Module.CountablyGenerated

namespace Module.CountablyGenerated.IsDirectSum

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A countably generated module is the one-term independent sum of a countably generated
submodule. -/
@[stacks 05A6 "one-summand decomposition"]
theorem of_countablyGenerated (hM : Module.CountablyGenerated R M) :
    Module.CountablyGenerated.IsDirectSum.{u, v, 0} R M := sorry

/-- The canonical direct-sum predicate transports across a linear equivalence. -/
theorem of_linearEquiv (e : M ≃ₗ[R] N)
    (hN : Module.CountablyGenerated.IsDirectSum.{u, w, x} R N) :
    Module.CountablyGenerated.IsDirectSum.{u, v, x} R M := sorry

end Module.CountablyGenerated.IsDirectSum

namespace Module.IsDirectSumOfCountablyGenerated

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A countably generated module is the one-term direct sum of a countably generated submodule. -/
@[stacks 05A6 "one-summand decomposition"]
theorem of_countablyGenerated (hM : Module.CountablyGenerated R M) :
    Module.IsDirectSumOfCountablyGenerated.{u, v, 0} R M := sorry

/-- A direct-sum decomposition into countably generated submodules transports across a linear
equivalence. -/
theorem of_linearEquiv (e : M ≃ₗ[R] N)
    (hN : Module.IsDirectSumOfCountablyGenerated.{u, w, x} R N) :
    Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M := sorry

end Module.IsDirectSumOfCountablyGenerated
