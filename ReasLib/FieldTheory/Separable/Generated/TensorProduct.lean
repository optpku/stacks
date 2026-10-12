/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import ReasLib.RingTheory.Algebra.TensorProduct.Reduced
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Reduced tensor products of separable-over extensions

This leaf owns the tensor-product consequence of `Algebra.IsSeparableOver`.
The field-level geometric-reducedness bridge is kept in
`Generated.GeometricallyReduced`, so consumers that only need the field
predicate do not import tensor-product support accidentally.

@stack 030U
-/

open scoped TensorProduct

namespace Algebra.IsSeparableOver

universe u v w

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]

/-- Lemma 10.43.6 (Tag 030U): tensoring a reduced `k`-algebra with a field extension separable
over `k` in the Stacks sense yields a reduced algebra.  This also covers the
source's separably generated alternative through
`Algebra.IsSeparablyGenerated.isSeparableOver`. -/
@[stacks 030U]
theorem isReduced_tensorProduct [IsSeparableOver k K] [IsReduced S] :
    IsReduced (K ⊗[k] S) := sorry

/-- Explicit-hypothesis form of `isReduced_tensorProduct`; use this when reducedness is data rather
than a globally installed proposition instance. -/
@[stacks 030U "explicit reducedness bridge"]
theorem isReduced_tensorProduct_of
    (hsep : IsSeparableOver k K) (hS : IsReduced S) :
    IsReduced (K ⊗[k] S) := sorry

end Algebra.IsSeparableOver
