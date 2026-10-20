/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Regular

/-- Regularity of schemes is local for the étale precoverage. -/
instance isLocalEtale :
    ObjectProperty.IsLocal (Scheme.Regular : ObjectProperty Scheme.{u})
      Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.Regular
