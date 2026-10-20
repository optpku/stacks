/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.NormalCurve.Nagata
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 32.17.3: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a quasi-compact morphism
of schemes locally of finite type over `S`. Then `f` is proper if and only if the Nagata-base
one-dimensional normal-curve valuative test has a unique dotted lift. -/
@[stacks 0GWX] #check
  (@AlgebraicGeometry.NormalCurvePunctureValuativeCriterion.isProper_iff_existsUnique :
    ∀ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY],
      f ≫ pY = pX →
        (IsProper f ↔
          AlgebraicGeometry.NormalCurvePunctureValuativeCriterion.ExistsUnique pX pY f))
