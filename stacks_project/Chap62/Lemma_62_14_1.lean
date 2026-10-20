/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Composition
import StacksCheckRecall

/-!
# Well-definedness of composition of relative cycles

This file records that composition of fibre-cycle families preserves the
relative-cycle condition, inducing a bilinear map on the groups `z(X/Y, r)`
and `z(Y/S, e)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 62.14.1: if `α` is a relative `r`-cycle on `X / Y` and `β` is a
relative `e`-cycle on `Y / S`, with `S` locally Noetherian and `X ⟶ Y ⟶ S`
locally of finite type, then the composite family is a relative
`(r + e)`-cycle on `X / S`. -/
@[stacks 0H6R] #check (AlgebraicGeometry.RelativeCycle.isRelative_comp :
  ∀ {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e),
    AlgebraicGeometry.RelativeCycle.IsRelative α →
    AlgebraicGeometry.RelativeCycle.IsRelative β →
    AlgebraicGeometry.RelativeCycle.IsRelative (AlgebraicGeometry.RelativeCycle.comp α β))
