/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

universe u

namespace AlgebraicGeometry

/-- A group scheme over a scheme `S` is an internal group object in the category of
schemes over `S`. -/
public abbrev GroupScheme (S : Scheme.{u}) : Type (u + 1) :=
  CategoryTheory.Grp (CategoryTheory.Over S)

namespace GroupScheme

/-- The base change of a group scheme along a morphism of base schemes. -/
public noncomputable def baseChange {S T : Scheme.{u}} (G : GroupScheme S) (f : T ⟶ S) :
    GroupScheme T :=
  (CategoryTheory.Over.pullback f).mapGrp.obj G

/-- The underlying object of a base-changed group scheme is the pullback of the
underlying object of the original group scheme. -/
@[simp]
public theorem baseChange_X {S T : Scheme.{u}} (G : GroupScheme S) (f : T ⟶ S) :
    (baseChange G f).X = (CategoryTheory.Over.pullback f).obj G.X := sorry

end GroupScheme

end AlgebraicGeometry
