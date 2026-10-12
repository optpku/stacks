/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

@[expose] public section

universe u w

namespace AlgebraicGeometry.StandardTopology

/-- The category of `Type w`-valued sheaves on the big `τ` site of `S`. -/
abbrev BigTopos (τ : StandardTopology) (S : Scheme.{u}) :=
  CategoryTheory.Sheaf (overTopology τ S) (Type w)

end AlgebraicGeometry.StandardTopology
