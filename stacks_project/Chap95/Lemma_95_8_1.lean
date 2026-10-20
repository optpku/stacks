/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType
import StacksCheckRecall

/-!
# Lemma 95.8.1

The functor `p_ft : Spaces_ft ⥤ (Sch/S)_fppf` satisfies conditions (1), (2) and
(3) of Stacks Definition 8.4.1: it is a stack.
-/

@[expose] public section

universe u

/- Lemma 95.8.1: the projection from the full category of finite-type algebraic
spaces over schemes over `S` satisfies fibredness, the Hom-sheaf condition, and
effective descent for objects on the fppf site. -/
@[stacks 04UD] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.instIsStackOnSite :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.IsStack.OnSite (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType.p S))
