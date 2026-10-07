module

public import stacks_project.Chap03.Lemma_3_9_1_Size

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.1. For every cardinal `κ`, there exists a set `A` of schemes such that every
scheme `S` with `size S ≤ κ` is isomorphic to some member of `A`. -/
@[stacks 000I]
theorem exists_small_of_size_le (κ : Cardinal.{u}) :
    ∃ (A : Type u) (X : A → Scheme.{u}),
      ∀ S : Scheme.{u}, S.size ≤ κ → ∃ a, Nonempty (X a ≅ S) := sorry

end AlgebraicGeometry.Scheme
