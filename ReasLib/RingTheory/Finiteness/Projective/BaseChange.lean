/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Base Change of Finite Projective Modules

This leaf records the semiring-level preservation of finite projectivity by
extension of scalars.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FiniteProjective

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable [AddCommMonoid M] [Module R M]

/-- Tag `00JH`: finite projectivity is preserved by scalar extension. -/
@[stacks 00JH "finite projective module base change"]
theorem baseChange (hM : Module.FiniteProjective R M) :
    Module.FiniteProjective S (S ⊗[R] M) := by
  letI := hM.finite
  letI := hM.projective
  exact ⟨inferInstance, inferInstance⟩

end Module.FiniteProjective
