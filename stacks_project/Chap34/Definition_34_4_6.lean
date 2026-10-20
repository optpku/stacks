/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Sites.Etale
import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 34.4.6: a big étale site is an explicit chosen small presentation of the
étale precoverage on schemes. -/
@[stacks 021A] #check
  (AlgebraicGeometry.ChosenBigSite.{u, v} AlgebraicGeometry.Scheme.etalePrecoverage :
    Type (max (u + 1) (v + 1)))
