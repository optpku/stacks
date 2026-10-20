module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAction

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right Algebra.TensorProduct.RightAction

universe u v w

namespace FixedPoints.Tensor

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

/-- For a prime lying over a prime under fixed-point tensor base change, the inertia subgroups agree. -/
theorem inertia_eq_of_liesOver
    [Finite G]
    (q : Ideal R) [q.IsPrime]
    (q' : Ideal (A ⊗[FixedPoints.subring R G] R))
    [q'.IsPrime] [q'.LiesOver q] :
    q.inertia G = q'.inertia G := sorry

end FixedPoints.Tensor
