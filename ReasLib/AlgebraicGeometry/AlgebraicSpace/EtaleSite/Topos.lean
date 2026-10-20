/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- The small étale topos of an algebraic space is the category of set-valued sheaves
on its small étale site of scheme charts. -/
abbrev topos {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  CategoryTheory.Sheaf (topology X) (Type w)

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
