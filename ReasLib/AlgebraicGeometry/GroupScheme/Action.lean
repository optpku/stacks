/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

/-- The category of actions of a group scheme over a scheme, with equivariant morphisms. -/
abbrev Action {S : Scheme.{u}} (G : Grp (Over S)) : Type (u + 1) :=
  Mod (Over S) G.X

end AlgebraicGeometry.GroupScheme
