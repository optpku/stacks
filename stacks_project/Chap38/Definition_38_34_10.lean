/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 38.34.10: a big h site is an explicit chosen small presentation
of the h precoverage on schemes, containing prescribed seed schemes and h
covering families. -/
@[stacks 0ETZ] #check (AlgebraicGeometry.ChosenBigHSite.{u, v} :
  Type (max (u + 1) (v + 1)))
