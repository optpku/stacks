/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.RingHom

/-!
# Opposite scalars on modules over a commutative semiring

`open scoped Module.CommOpposite` supplies the opposite action obtained by
restricting the given left action along `Rᵐᵒᵖ →+* R`. This is useful for
commutative trivial square-zero extensions of ordinary left modules.

The action is scoped: importing this file does not install a second global
right action on every module. Its low priority preserves existing actions,
in particular mathlib's right multiplication action `Semiring.toOppositeModule`.
For an independently supplied right action, centrality remains a hypothesis.
-/

@[expose] public section

universe u v

namespace Module.CommOpposite

/-- Restrict the left action along the opposite-to-original homomorphism. -/
scoped instance (priority := 100) module (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite mul_comm)

/-- The restricted opposite action agrees with the given left action. -/
scoped instance (priority := 100) isCentralScalar (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M] : IsCentralScalar R M where
  op_smul_eq_smul _ _ := rfl

/-- Computation rule for the restricted opposite action. -/
theorem smul_def {R : Type u} {M : Type v} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (r : Rᵐᵒᵖ) (m : M) :
    r • m = MulOpposite.unop r • m := rfl

end Module.CommOpposite
