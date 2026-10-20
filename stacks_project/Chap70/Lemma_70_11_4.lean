/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.ClosedImmersionApproximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.4: a closed immersion `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose transition maps
are closed immersions and whose structure maps `X_i ⟶ Y` are closed immersions
of finite presentation. -/
@[stacks 0A0U] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_closedImmersionApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsClosedImmersion f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      ∃ (I : Type u) (preorderI : Preorder I) (nonemptyI : Nonempty I)
        (directedI : IsDirected I (· ≤ ·)) (D : OrderDual I ⥤ AlgebraicSpace S)
        (π : (Functor.const (OrderDual I)).obj X ⟶ D)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y),
        IsClosedImmersionApproximation f D π σ)
