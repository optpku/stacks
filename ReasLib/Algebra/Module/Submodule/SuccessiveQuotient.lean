/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Successive quotients of indexed submodule families

This leaf owns the deterministic lower-stage and successive-quotient constructions for an
indexed submodule family.  Monotonicity, exhaustiveness, and well-foundedness are conditions on
particular applications and are therefore left to their consuming theorems.
-/

@[expose] public section

universe u v w

namespace Submodule

section LowerStage

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Preorder ι]

/-- The supremum of the stages strictly preceding `e`. -/
@[stacks 0D1U "lower stage"]
def lowerStage (F : ι → Submodule R M) (e : ι) : Submodule R M :=
  ⨆ e' : Set.Iio e, F e'

end LowerStage

section SuccessiveQuotient

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} [Preorder ι]

/-- The quotient of the stage at `e` by the part contributed by strictly earlier stages. -/
@[stacks 0D1U "successive quotient"]
abbrev successiveQuotient (F : ι → Submodule R M) (e : ι) : Type v :=
  (F e : Type v) ⧸
    Submodule.comap (F e).subtype (lowerStage F e)

end SuccessiveQuotient

end Submodule
