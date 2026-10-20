module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Presentation and Tensor Products of Families

This file characterizes finitely presented modules by the canonical comparison
from tensoring a product to the product of the tensor products.  The forward
API is stated over commutative semirings and with independent universes; the
converse is isolated in the ring setting where the finite-presentation
criterion is available.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace TensorProduct

section Naturality

variable {R : Type u} [CommSemiring R]
variable {X : Type v} [AddCommMonoid X] [Module R X]
variable {Y : Type w} [AddCommMonoid Y] [Module R Y]

/-- The product comparison map is natural in its left tensor factor. -/
theorem piRightHom_rTensor_apply (f : X →ₗ[R] Y) {A : Type*} {Q : A → Type x}
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)] (t : X ⊗[R] (∀ a, Q a)) :
    piRightHom R R Y Q (f.rTensor (∀ a, Q a) t) =
      fun a ↦ f.rTensor (Q a) ((piRightHom R R X Q t) a) := sorry

/-- The scalar-family comparison map is natural in its left tensor factor. -/
theorem piScalarRightHom_rTensor_apply (f : X →ₗ[R] Y) (A : Type*)
    (t : X ⊗[R] (A → R)) :
    piScalarRightHom R R Y A (f.rTensor (A → R) t) =
      fun a ↦ f ((piScalarRightHom R R X A t) a) := sorry

end Naturality

end TensorProduct

namespace Module.Finite

/-- A finite module maps onto every product of its coordinatewise tensor
products. -/
theorem piRightHom_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] [Module.Finite R M]
    {A : Type w} (Q : A → Type x) [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R M Q) := sorry

/-- A finite module maps onto the product indexed by any scalar-valued family. -/
theorem piScalarRightHom_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (A : Type w) :
    Function.Surjective (TensorProduct.piScalarRightHom R R M A) := sorry

/-- Finite generation is equivalent to surjectivity of every tensor-product
comparison map into a product. -/
theorem iff_piRightHom_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔
      ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
          [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)],
        Function.Surjective (TensorProduct.piRightHom R R M Q) := sorry

/-- Finite generation can be tested using only scalar-valued product
comparison maps. -/
theorem iff_piScalarRightHom_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔
      ∀ A : Type (max u v w),
        Function.Surjective (TensorProduct.piScalarRightHom R R M A) := sorry

/-- Finite generation is equivalent to
surjectivity of the product comparison map for arbitrary families, constant
families, or scalar-valued families. -/
@[stacks 059J]
theorem tfae_piRightHom_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] :
    List.TFAE
      [ Module.Finite R M,
        ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
            [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max u v w)) (Q : Type (max u x))
            [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ A : Type (max u v w),
          Function.Surjective (TensorProduct.piScalarRightHom R R M A) ] := sorry

end Module.Finite

namespace Module.FinitePresentation

section Semiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A finitely presented module commutes with arbitrary products under tensor
product. -/
theorem piRightHom_bijective [Module.FinitePresentation R M]
    {A : Type w} (Q : A → Type x) [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)] :
    Function.Bijective (TensorProduct.piRightHom R R M Q) := sorry

/-- The scalar-family comparison map is bijective for every finitely presented
module. -/
theorem piScalarRightHom_bijective [Module.FinitePresentation R M] (A : Type w) :
    Function.Bijective (TensorProduct.piScalarRightHom R R M A) := sorry

end Semiring

end Module.FinitePresentation

namespace Module.FinitePresentation

section Ring

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite presentation is equivalent to bijectivity of every tensor-product
comparison map into a product. -/
theorem iff_piRightHom_bijective :
    Module.FinitePresentation R M ↔
      ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
          [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
        Function.Bijective (TensorProduct.piRightHom R R M Q) := sorry

/-- Finite presentation can be tested using only scalar-valued product
comparison maps. -/
theorem iff_piScalarRightHom_bijective :
    Module.FinitePresentation R M ↔
      ∀ A : Type (max u v w),
        Function.Bijective (TensorProduct.piScalarRightHom R R M A) := sorry

/-- Finite presentation is equivalent to
bijectivity of the product comparison map for arbitrary families, constant
families, or scalar-valued families. -/
@[stacks 059K]
theorem tfae_piRightHom_bijective :
    List.TFAE
      [ Module.FinitePresentation R M,
        ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
            [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Bijective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max u v w)) (Q : Type (max u x)) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ A : Type (max u v w),
          Function.Bijective (TensorProduct.piScalarRightHom R R M A) ] := sorry

end Ring

end Module.FinitePresentation
