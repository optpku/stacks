/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

@[expose] public section

/-!
# Definition 34.5.6

This chapter entry records a chosen set-sized presentation of a big smooth site.
-/

universe u v

/- Definition 34.5.6: a big smooth site is a chosen set-sized big-site presentation whose
carrier is identified with `Sch_α` of Tag 000J and whose coverings come from the
smooth precoverage on schemes. -/
@[stacks 03WY] #check
  (AlgebraicGeometry.SchAlphaBigSite.{u, v}
    (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Smooth)) :
      Type (max (u + 1) (v + 1)))
