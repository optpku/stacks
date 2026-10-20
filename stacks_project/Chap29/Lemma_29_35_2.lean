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

/- Lemma 29.35.2 (1): a morphism of schemes is unramified if and only if it is locally of finite
type and its sheaf of relative differentials vanishes. -/
@[stacks 02G5] #check
  (AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Unramified f ↔
        AlgebraicGeometry.LocallyOfFiniteType f ∧
          CategoryTheory.Limits.IsZero (Ω[f.toShHom]))

/- Lemma 29.35.2 (2): a morphism of schemes is G-unramified if and only if it is locally of
finite presentation and its sheaf of relative differentials vanishes. -/
@[stacks 02G5] #check
  (AlgebraicGeometry.GUnramified.iff_differentials :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.GUnramified f ↔
        AlgebraicGeometry.LocallyOfFinitePresentation f ∧
          CategoryTheory.Limits.IsZero (Ω[f.toShHom]))
