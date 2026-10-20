module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensionality for ring maps out of tensor products

This leaf records the pure-tensor extensionality principle for arbitrary ring
homomorphisms out of an algebra tensor product.  It is deliberately owned by
`RingHom`, rather than by one application-specific tensor construction.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace RingHom

/-- Ring homomorphisms out of an algebra tensor product agree when they agree
on every pure tensor. -/
@[stacks 00R0 "tensor-product ring-hom extensionality"]
theorem ext_of_tmul
    {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra R A] [Algebra R B]
    {f g : A ⊗[R] B →+* C}
    (h : ∀ a : A, ∀ b : B, f (a ⊗ₜ[R] b) = g (a ⊗ₜ[R] b)) :
    f = g := sorry

end RingHom
