/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action

/-!
# Actions of group algebraic spaces

An action of a group algebraic space `G` over an algebraic space `B` is a module
object for `G.X` in the cartesian monoidal slice `Over B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- A module object structure on an algebraic space over `B` determines a bundled
action of the group algebraic space `G`. -/
#check (AlgebraicGeometry.GroupAlgebraicSpace.Action.of :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : Over B) [ModObj G.X X], GroupAlgebraicSpace.Action G)
