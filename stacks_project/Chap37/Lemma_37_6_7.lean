/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.6.7: a scheme morphism is formally unramified if and only if its sheaf of
relative differentials is a zero object. -/
@[stacks 02H9] #check
  (AlgebraicGeometry.formallyUnramified_iff_isZero_relativeDifferentials :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.FormallyUnramified f ↔
        CategoryTheory.Limits.IsZero (Ω[f.toShHom]))
