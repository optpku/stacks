module

public import Mathlib.RingTheory.AlgebraTower

@[expose] public section

/-!
# Injectivity in towers of algebras

This file contains elementary consequences of the compatibility data carried by
`IsScalarTower` that are useful independently of any particular algebraic invariant.
-/

namespace IsScalarTower

universe u v w

/-- In a tower of algebras, the composite algebra map is injective when both consecutive algebra
maps are injective. -/
theorem algebraMap_injective_of_injective
    {R : Type u} {S : Type v} {A : Type w}
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (hRS : Function.Injective (algebraMap R S)) (hSA : Function.Injective (algebraMap S A)) :
    Function.Injective (algebraMap R A) := by
  rw [IsScalarTower.algebraMap_eq R S A]
  exact hSA.comp hRS

end IsScalarTower
