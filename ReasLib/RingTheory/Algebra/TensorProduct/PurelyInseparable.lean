/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import ReasLib.FieldTheory.PurelyInseparable.Lift

/-!
# Reducedness transport along purely inseparable lifts

The lift itself is the canonical field-theoretic owner.  This leaf owns only the ring-level
consequence needed when a reduced tensor product is pulled back through such a lift.

@stack 030V
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace FieldExtension.PurelyInseparable.Lift

/-- Lemma 10.44.4 (Tag 030V): reducedness of the base tensor product descends through a finite
purely inseparable lift whose top extension is separably generated. -/
@[stacks 030V]
theorem isReduced_tensorProduct
    {k : Type u} {K : Type v} {k' : Type w} {K' : Type x} {S : Type y}
    [Field k] [Field K] [Field k'] [Field K'] [CommRing S]
    [Algebra k K] [Algebra k k'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [Algebra k S] [IsScalarTower k K K'] [IsScalarTower k k' K']
    (hlift : FieldExtension.PurelyInseparable.Lift k K k' K')
    [IsReduced (k' ⊗[k] S)] :
    IsReduced (K ⊗[k] S) := sorry

/-- Explicit-hypothesis form of `isReduced_tensorProduct`; use this bridge when the base tensor
product's reducedness is proposition-valued data rather than an installed instance. -/
@[stacks 030V "explicit purely-inseparable reducedness bridge"]
theorem isReduced_tensorProduct_of
    {k : Type u} {K : Type v} {k' : Type w} {K' : Type x} {S : Type y}
    [Field k] [Field K] [Field k'] [Field K'] [CommRing S]
    [Algebra k K] [Algebra k k'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [Algebra k S] [IsScalarTower k K K'] [IsScalarTower k k' K']
    (hlift : FieldExtension.PurelyInseparable.Lift k K k' K')
    (hbase : IsReduced (k' ⊗[k] S)) :
    IsReduced (K ⊗[k] S) := sorry

end FieldExtension.PurelyInseparable.Lift
