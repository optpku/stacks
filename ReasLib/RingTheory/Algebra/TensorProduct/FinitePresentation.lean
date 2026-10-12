/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import ReasLib.RingTheory.Algebra.TensorProduct.RightMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Presentation and Right Tensor Products

This leaf records the finite-presentation transport from the usual left
base-change orientation to a right-oriented tensor product.
-/

@[expose] public section

universe u w

open scoped TensorProduct Algebra.TensorProduct.Right

namespace Algebra

/-- Right tensoring a finitely presented algebra yields a finitely presented algebra over the
right tensor factor. -/
@[stacks 05LI "tensor-product finite-presentation base change"]
theorem finitePresentation_tensor_right {R : Type u} [CommRing R] {Q : Type*} [CommRing Q]
    [Algebra R Q] [Algebra.FinitePresentation R Q] {T : Type w} [CommRing T] [Algebra R T] :
    Algebra.FinitePresentation T (Q ⊗[R] T) := sorry

end Algebra

namespace Algebra.TensorProduct

/-- Base changing a finitely presented algebra homomorphism along an arbitrary
commutative base algebra remains finitely presented. -/
@[stacks 05LI "tensor-product finite-presentation base change"]
theorem map_finitePresentation
    {R : Type u} [CommRing R] {B C : Type*} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (g : B →ₐ[R] C) (hg : g.FinitePresentation)
    {T : Type w} [CommRing T] [Algebra R T] :
    (map g (AlgHom.id R T)).FinitePresentation := sorry

end Algebra.TensorProduct
