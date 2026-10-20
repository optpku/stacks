/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.SerreCondition
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.CohenMacaulay

/-- Cohen–Macaulayness is local for the smooth precoverage. -/
instance smoothLocal :
    ObjectProperty.IsLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.CohenMacaulay
