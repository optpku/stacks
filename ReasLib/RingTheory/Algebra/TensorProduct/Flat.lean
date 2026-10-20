module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Flatness of Right Tensor Products

@stack 037N
@stack 0CWE

This leaf transports mathlib's left-oriented base-change flatness across
`Algebra.TensorProduct.commRight`.  It deliberately provides the result as a
theorem rather than a global instance: the right algebra structure on a tensor
product is a chosen presentation and is not globally canonical.
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct Algebra.TensorProduct.Right

namespace Algebra.TensorProduct

/-- The tensor product of two injective algebra morphisms is injective when the target of the
left map and the source of the right map are flat over the common base.  This is the
`AlgHom`-level form of `TensorProduct.map_injective_of_flat_flat`. -/
@[stacks 037N "tensor-product map injectivity support"]
theorem map_injective_of_flat_flat
    {R : Type u} {A : Type v} {B : Type w} {C : Type x} {D : Type y}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring C] [CommSemiring D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    [Module.Flat R C] [Module.Flat R B]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := sorry

/-- A flat `R`-algebra remains flat after base change when the tensor product is written with the
base-change algebra on the left and the new scalar ring on the right. -/
theorem flat_right
    {R : Type u} {S : Type v} {A : Type w}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Module.Flat R A] :
    Module.Flat S (A ⊗[R] S) := sorry

/-- A faithfully flat `R`-algebra remains faithfully flat after base change when the tensor
product is written with the base-change algebra on the left and the new scalar ring on the
right. -/
@[stacks 0CWE "faithfully flat right tensor product support"]
theorem faithfullyFlat_right
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] :
    Module.FaithfullyFlat S (A ⊗[R] S) := sorry

/-- The right tensor inclusion is flat when the left tensor factor is flat over the base ring. -/
theorem includeRight_flat
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] [Module.Flat R A] :
    (includeRight : S →ₐ[R] A ⊗[R] S).toRingHom.Flat := sorry

end Algebra.TensorProduct
