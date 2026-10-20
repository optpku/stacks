/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.RelativeFinitePresentationApproximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.10.2: a morphism of algebraic spaces over a scheme `S`, with
quasi-compact, absolutely quasi-separated source and absolutely quasi-separated
target, is a directed inverse limit of algebraic spaces of finite presentation
over the target with affine transition morphisms over the target. -/
@[stacks 09NS] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_relativeFinitePresentationApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsAbsolutelyQuasiSeparated Y],
      ∃ (I : Type u) (preorderI : Preorder I) (nonemptyI : Nonempty I)
        (directedI : IsDirected I (· ≤ ·)) (D : OrderDual I ⥤ AlgebraicSpace S)
        (π : (Functor.const (OrderDual I)).obj X ⟶ D)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y),
        AlgebraicGeometry.AlgebraicSpace.IsRelativeFinitePresentationApproximation
          f D π σ)
