/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- The category of `Type w`-valued sheaves on the small Zariski site of `S`. -/
abbrev SmallZariskiTopos (S : Scheme.{u}) :=
  CategoryTheory.Sheaf S.smallZariskiTopology (Type w)

end AlgebraicGeometry.Scheme
