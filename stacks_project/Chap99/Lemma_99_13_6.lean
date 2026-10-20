/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.LimitPreserving
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Spaces

universe u

/- Lemma 99.13.6: the stack of finite-presentation, flat, proper algebraic spaces
is limit preserving. -/
@[stacks 0D1I] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.isLimitPreserving :
    ∀ (S : Scheme.{u}) {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
      (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
      (hpt : IsAffine c.pt.left),
      (∀ x : (pFpFlatProperGroupoids S).Fiber c.pt,
        ∃ (i : I) (xi : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
          IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
        ∀ (i : I) (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
          Nonempty (IsColimit (FpFlatProperGroupoids.homCocone S c x y)))
