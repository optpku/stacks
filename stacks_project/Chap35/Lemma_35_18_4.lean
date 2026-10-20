/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular.Smooth
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 35.18.4: regularity of schemes is local for the smooth precoverage. -/
@[stacks 036D] #check
  (AlgebraicGeometry.Scheme.Regular.smoothLocal :
    ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.Regular : ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
