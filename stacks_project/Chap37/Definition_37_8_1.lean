/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.8.1: A scheme morphism is formally étale exactly when every commutative
square from an affine first-order thickening has a unique lift. -/
@[stacks 02HG] #check (AlgebraicGeometry.FormallyEtale.iff_existsUnique_lift :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.FormallyEtale f ↔
      ∀ {T T' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
        [AlgebraicGeometry.IsAffine T'] (i : T ⟶ T') [AlgebraicGeometry.IsClosedImmersion i],
          i.ker ^ 2 = ⊥ → ∀ (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
            Nonempty (Unique sq.LiftStruct))
