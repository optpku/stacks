/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.LimitPreserving

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.CohStack

universe u

/- Lemma 99.5.6: if `f : X ⟶ B` is of finite presentation and `B ⟶ S` is
locally of finite presentation, the coherent-sheaf fibration is limit preserving. -/
@[stacks 08KD] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.isLimitPreserving :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left),
    (∀ x : (p f).Fiber c.pt, ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p f).Fiber (D.obj i)),
        Nonempty (IsColimit (DirectedSystem.homCocone (p f) c x y)))
