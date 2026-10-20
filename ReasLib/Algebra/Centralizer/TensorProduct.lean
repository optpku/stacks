module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Subalgebra

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {A₂ : Type w} [Ring A₂] [Algebra k A₂]

/-- The centralizer of a tensor-product subalgebra is the tensor product of the
centralizers of its factors. -/
theorem centralizer_tensorProduct_subalgebra_eq
    (B : Subalgebra k A) (B₂ : Subalgebra k A₂) :
    centralizer k (Algebra.TensorProduct.map B.val B₂.val).range =
      (Algebra.TensorProduct.map (centralizer k (B : Set A)).val
        (centralizer k (B₂ : Set A₂)).val).range := sorry

end Subalgebra
