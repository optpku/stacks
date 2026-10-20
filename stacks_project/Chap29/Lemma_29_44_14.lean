/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.44.14 (1): if `f ≫ g` is finite and `g` is separated, then `f` is finite. -/
@[stacks 035D] #check
  (AlgebraicGeometry.IsFinite.of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.IsFinite (f ≫ g)] [AlgebraicGeometry.IsSeparated g],
      AlgebraicGeometry.IsFinite f)

/- Lemma 29.44.14 (2): if `f ≫ g` is integral and `g` is separated, then `f` is integral. -/
@[stacks 035D] #check
  (AlgebraicGeometry.IsIntegralHom.of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.IsIntegralHom (f ≫ g)] [AlgebraicGeometry.IsSeparated g],
      AlgebraicGeometry.IsIntegralHom f)
