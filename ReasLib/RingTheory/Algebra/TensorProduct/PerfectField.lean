/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Perfect
public import ReasLib.RingTheory.Algebra.TensorProduct.Reduced
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Perfect
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced tensor products over perfect fields

This leaf owns the perfect-field specialization of tensor-product reducedness.
The general injectivity and geometric-reducedness interfaces live in
`ReasLib.RingTheory.Algebra.TensorProduct.Reduced`; keeping this specialization
separate lets consumers of the 034N API avoid importing perfect-field results.

@stack 00I4
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Lemma 10.45.6, tag `00I4`: tensoring two reduced commutative algebras over
a perfect field yields a reduced algebra. -/
@[stacks 00I4]
theorem isReduced_of_perfectField
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [PerfectField k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsReduced R] [IsReduced S] :
    IsReduced (R ⊗[k] S) := sorry

end Algebra.TensorProduct
