/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupScheme.Action
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable (S : Scheme.{u}) (G : Grp (Over S))

/- Definition 39.10.1: The category of actions of the group scheme `G` on schemes over
`S`; its morphisms are the `G`-equivariant morphisms over `S`. -/
@[stacks 022Z] #check (AlgebraicGeometry.GroupScheme.Action G : Type (u + 1))

/- Every scheme of generalized points of a `G`-scheme inherits the induced action of the
corresponding group of generalized points of `G`. -/
#check CategoryTheory.Hom.mulAction

/- A morphism in `AlgebraicGeometry.GroupScheme.Action G` is equivariant for those induced
pointwise actions. -/
#check CategoryTheory.IsModHom.mulActionHom
