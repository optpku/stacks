module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Faithfully flat universally injective algebra maps

This file connects faithfully flat algebras with tensor-stable injectivity of their algebra
linear maps.
-/

@[expose] public section

universe u v z

namespace Module.FaithfullyFlat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The algebra linear map of a faithfully flat `R`-algebra `S` is universally injective. -/
@[stacks 05CK]
theorem universallyInjective_algebraLinearMap [Module.FaithfullyFlat R S] :
    LinearMap.UniversallyInjective.{u, u, v, z} (Algebra.linearMap R S) := by
  intro Q _ _
  apply Function.Injective.of_comp_right ?_ (TensorProduct.lid R Q).symm.surjective
  have h : TensorProduct.mk R S Q 1 =
      (Algebra.linearMap R S).rTensor Q ∘ (TensorProduct.lid R Q).symm := by
    ext
    simp
  rw [← h]
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) Q

end Module.FaithfullyFlat
