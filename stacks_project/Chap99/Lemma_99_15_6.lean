/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LimitPreserving
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor.Fiber

universe u

/- Lemma 99.15.6. The stack of curves is limit preserving. -/
@[stacks 0D55] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isLimitPreserving :
    ∀ (S : Scheme.{u}) {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
      (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
      (hpt : IsAffine c.pt.left),
      (∀ x : (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S).Fiber c.pt,
        ∃ (i : I)
          (xi : (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S).Fiber (D.obj i)),
          IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
        ∀ (i : I)
          (x y : (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S).Fiber (D.obj i)),
          Nonempty (IsColimit
            (CategoryTheory.Functor.Fiber.DirectedSystem.homCocone
              (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S) c x y)))
