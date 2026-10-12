/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-! # Degree of a Central Simple Algebra

The dimension of a finite-dimensional central simple k-algebra is always a perfect
square. The degree is defined as the square root of this dimension.

## Main declarations

- `CSA.finrank_isSquare` — `[A:k]` is a perfect square
- `CSA.degree` — the square root of `[A:k]`
- `CSA.degree_sq_eq_finrank` — `degree² = finrank`

## References

- [Stacks Project, Tag 074N](https://stacks.math.columbia.edu/tag/074N)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace CSA

section

variable {k : Type u} [Field k]

/-- The `k`-dimension of a finite central simple algebra is a perfect square. -/
theorem finrank_isSquare (A : CSA.{u, v} k) : IsSquare (Module.finrank k A) := by
  let K := AlgebraicClosure k
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A.baseChange K)
  have hbase : Module.finrank K (A.baseChange K) = Module.finrank k A := by
    change Module.finrank K (K ⊗[k] A) = Module.finrank k A
    exact Module.finrank_baseChange
  refine ⟨n, ?_⟩
  calc
    Module.finrank k A = Module.finrank K (A.baseChange K) := hbase.symm
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := e.toLinearEquiv.finrank_eq
    _ = n * n := by
      simpa using (Module.finrank_matrix K K (Fin n) (Fin n))

/-- The degree of a finite central simple algebra: the square root of its dimension. -/
noncomputable def degree (A : CSA.{u, v} k) : ℕ :=
  Nat.sqrt (Module.finrank k A)

/-- The square of the degree equals the dimension over the base field. -/
theorem degree_sq_eq_finrank (A : CSA.{u, v} k) :
    A.degree ^ 2 = Module.finrank k A := by
  rcases A.finrank_isSquare with ⟨n, hn⟩
  rw [degree, hn, Nat.sqrt_eq, pow_two]

end

end CSA

end
