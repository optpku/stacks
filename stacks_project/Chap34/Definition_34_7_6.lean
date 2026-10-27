/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksCheckRecall

universe u v

/- Definition 34.7.6: a big fppf site is a chosen set-sized big-site presentation whose
carrier is identified with `Sch_α` of Tag 000J and whose coverings come from the
fppf precoverage on schemes. -/
@[stacks 021R] #check
  (AlgebraicGeometry.SchAlphaBigSite.{u, v} AlgebraicGeometry.Scheme.fppfPrecoverage :
    Type (max (u + 1) (v + 1)))
