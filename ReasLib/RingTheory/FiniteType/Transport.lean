/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of finite type along algebra equivalences

This leaf contains only the neutral base-change principle for finite-type algebras.  Graded-algebra
specializations belong in their grading-specific leaves and depend on this file.
-/

@[expose] public section

universe u v w

namespace Algebra.FiniteType

variable {R T A : Type*}
variable [CommSemiring R] [CommSemiring T] [Semiring A]
variable [Algebra R T] [Algebra R A]

/-- Change the base of a finite-type algebra along an algebra equivalence.

The target algebra structure over `T` and its scalar tower over `R` are explicit assumptions:
the equivalence changes only the base, while it does not silently replace the given `T`-action on
`A`. -/
@[stacks 07Z2 "finite type after an algebra-equivalent base change"]
theorem of_algEquiv [Algebra T A] [IsScalarTower R T A]
    (e : R ≃ₐ[R] T) [Algebra.FiniteType T A] :
    Algebra.FiniteType R A := sorry

end Algebra.FiniteType
