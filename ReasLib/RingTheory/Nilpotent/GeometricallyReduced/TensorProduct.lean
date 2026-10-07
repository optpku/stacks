module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of geometrically reduced algebras

This leaf owns the intrinsic field-extension criteria for
`Algebra.IsGeometricallyReduced`.  Generic tensor-product transports remain in
`RingTheory.Algebra.TensorProduct.Reduced`; keeping the predicate criteria here
gives consumers a direct geometric-reducedness import without pulling in
unrelated injectivity lemmas.

@stack 030S
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.IsGeometricallyReduced

/-- Over a field, a commutative algebra is geometrically reduced exactly when every
field-extension tensor product is reduced. -/
@[stacks 030S]
theorem iff_forall_isReduced_tensorProduct
    {k : Type u} {S : Type v}
    [Field k] [CommRing S] [Algebra k S] :
    Algebra.IsGeometricallyReduced k S ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], IsReduced (K ⊗[k] S) := sorry

/-- Geometric reducedness is preserved by arbitrary field-extension base change. -/
@[stacks 030S "geometric reducedness base change"]
theorem baseChange
    {k : Type u} {K : Type v} {R : Type w}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    [Algebra.IsGeometricallyReduced k R] :
    Algebra.IsGeometricallyReduced K (K ⊗[k] R) := sorry

/-- Explicit-hypothesis form of `baseChange`; use this bridge when geometric reducedness is
available as a proposition value rather than an installed instance. -/
@[stacks 030S "explicit geometric-reducedness base-change bridge"]
theorem baseChange_of
    {k : Type u} {K : Type v} {R : Type w}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    (hR : Algebra.IsGeometricallyReduced k R) :
    Algebra.IsGeometricallyReduced K (K ⊗[k] R) := sorry

end Algebra.IsGeometricallyReduced
