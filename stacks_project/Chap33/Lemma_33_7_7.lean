/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.SeparableClosure
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.7.7 (Tag 0387): let `k` be a field, let `X` be a scheme over `k`, and let `ksep` be
a separable algebraic closure of `k`. Then `X` is geometrically connected over `k` if and only if
the base change `X ×[Spec k] Spec ksep` is connected. -/
@[stacks 0387]
#check (AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_baseChange_toSepClosure :
  ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) {ksep : Type u}
    [Field ksep] [Algebra k ksep] [IsSepClosure k ksep],
    AlgebraicGeometry.GeometricallyConnected f ↔
      ConnectedSpace
        (CategoryTheory.Limits.pullback f
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k ksep))) :
            AlgebraicGeometry.Scheme))
