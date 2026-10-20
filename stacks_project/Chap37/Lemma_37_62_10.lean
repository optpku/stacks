/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Smooth
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.62.10: in a commutative triangle of scheme morphisms, if `Y ⟶ S` is
smooth and `X ⟶ S` is a local complete intersection morphism, then `X ⟶ Y` is a
local complete intersection morphism. -/
@[stacks 069M] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_of_smooth_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
      (hcomm : f ≫ g = h) [AlgebraicGeometry.Smooth g]
      (hX : AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h),
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)
