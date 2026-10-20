/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- The category of `Type w`-valued sheaves on the small étale site of `S`. -/
abbrev SmallEtaleTopos (S : Scheme.{u}) :=
  CategoryTheory.Sheaf S.smallEtaleTopology (Type w)

end AlgebraicGeometry.Scheme
