/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.25.1: Let `k` be a field of characteristic zero and
`f : X ⟶ Spec (CommRingCat.of k)` a locally finite type morphism. If `Ω[f.toShHom]` is locally
free, then `f` is smooth. -/
@[stacks 04QN] #check
  (AlgebraicGeometry.instSmoothOfCharZeroOfIsLocallyFreeDifferentials :
    {X : Scheme.{u}} → {k : Type u} → [Field k] → [CharZero k] →
      (f : X ⟶ Spec (CommRingCat.of k)) → [LocallyOfFiniteType f] →
      [(Ω[f.toShHom]).IsLocallyFree] →
      Smooth f)
