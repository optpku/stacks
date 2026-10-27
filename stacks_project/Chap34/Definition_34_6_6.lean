/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 34.6.6

This chapter entry records a chosen set-sized presentation of a big syntomic site.
-/

universe u v

/- Definition 34.6.6: a big syntomic site is a chosen set-sized big-site presentation whose
carrier is identified with `Sch_α` of Tag 000J and whose coverings come from the
syntomic precoverage on schemes. -/
@[stacks 03X1] #check
  (AlgebraicGeometry.SchAlphaBigSite.{u, v}
    (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Syntomic)) :
      Type (max (u + 1) (v + 1)))
