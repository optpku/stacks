/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.37.5: if the base scheme `S` is affine, then an invertible module on `X` is
`f`-relatively ample if and only if it is ample on `X`. -/
@[stacks 01VK] #check
  (AlgebraicGeometry.relativelyAmple_iff_isAmple_of_isAffine :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
      [IsAffine S] [Scheme.Modules.Invertible L],
      RelativelyAmple f L ↔ Scheme.Modules.IsAmple L)
