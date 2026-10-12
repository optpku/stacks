/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BaseChange
public import Mathlib.Algebra.BrauerGroup.Defs

/-! # Splitting Fields of Central Simple Algebras

A central simple algebra A is split by a field extension K/k if the base change
A ⊗_k K becomes isomorphic to a matrix algebra over K.

## Main declarations

- `CSA.IsSplitBy` — the splitting predicate
- `CSA.isSplitBy_iff_exists_pnat` — equivalent formulation with positive matrix size

## References

- [Stacks Project, Tag 074Y](https://stacks.math.columbia.edu/tag/074Y)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/-- A central simple algebra `A` over `k` is split by a field extension `K/k` if
`A ⊗_k K ≃ₐ[K] Mₙ(K)` for some `n`. -/
def IsSplitBy (K : Type w) [Field K] [Algebra k K] : Prop :=
  ∃ n : ℕ, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- Splitting is equivalent to having a positive-size matrix presentation. -/
theorem isSplitBy_iff_exists_pnat (K : Type w) [Field K] [Algebra k K] :
    A.IsSplitBy K ↔
      ∃ n : ℕ+, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨n, ⟨e⟩⟩
    have hn : n ≠ 0 := by
      intro h
      subst h
      have : Subsingleton (A.baseChange K) := by
        exact e.toEquiv.subsingleton
      exact absurd (show (1 : (A.baseChange K)) = 0 from Subsingleton.elim _ _)
        (one_ne_zero)
    exact ⟨⟨n, Nat.pos_of_ne_zero hn⟩, ⟨e⟩⟩
  · rintro ⟨n, h⟩
    exact ⟨n, h⟩

end

end CSA

end
