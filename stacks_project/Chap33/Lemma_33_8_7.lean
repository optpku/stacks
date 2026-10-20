/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 33.8.7: a scheme `X` over a field `k` is geometrically irreducible over `k`
if and only if its self fiber product `X ×[Spec k] X` is irreducible. -/
@[stacks 0H8G] #check
  (AlgebraicGeometry.GeometricallyIrreducible.BaseChange.iff_selfFiberProduct :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      GeometricallyIrreducible f ↔ IrreducibleSpace ((pullback f f : Scheme.{u})))
