/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epicenters of commutative algebras

The epicenter is the equalizer of the two canonical maps from an algebra to
its tensor square.  It is useful independently of any chosen generators or
matrix presentation, which are kept in a separate leaf.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The epicenter of `S` over `R`: the largest `R`-subalgebra on which the
left and right maps to `S ⊗[R] S` agree. -/
@[stacks 04VZ "epicenter"]
def epicenter : Subalgebra R S :=
  AlgHom.equalizer
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)

/-- Membership in the epicenter is equality of the two canonical pure
tensors. -/
@[simp, stacks 04VZ "epicenter membership"]
theorem mem_epicenter (g : S) :
    g ∈ epicenter (R := R) (S := S) ↔
      g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  simp only [epicenter, AlgHom.mem_equalizer,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- The epicenter is the whole algebra exactly when the two canonical maps to
the tensor square agree. -/
@[stacks 04VZ "top epicenter"]
theorem epicenter_eq_top_iff_includeLeft_eq_includeRight :
    epicenter (R := R) (S := S) = ⊤ ↔
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
        Algebra.TensorProduct.includeRight := by
  exact AlgHom.equalizer_eq_top

end Algebra
