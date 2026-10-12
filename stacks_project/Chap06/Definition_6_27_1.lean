/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat
open scoped AlgebraicGeometry

universe u v

section

variable {X : TopCat.{u}}
variable {C : Type v} [Category C] [CategoryTheory.Limits.HasTerminal C]
variable (ℱ : X.Sheaf C)

/- Definition 6.27.1 (1): the skyscraper sheaf at `x` with value `A` is the canonical
project-facing owner `TopCat.Sheaf.Skyscraper.atPoint x A`. -/
@[stacks 009A "skyscraper sheaf with values in sets, abelian groups, or algebraic structures"]
#check TopCat.Sheaf.Skyscraper.atPoint

/- Definition 6.27.1 (2): a sheaf is a skyscraper sheaf if it is isomorphic to
`TopCat.Sheaf.Skyscraper.atPoint x A` for some point `x` and value `A`. -/
@[stacks 009A "sheaves isomorphic to a skyscraper sheaf"]
#check TopCat.Sheaf.IsSkyscraper ℱ

end

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}} (x : X)
variable (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
variable (ℱ : X.Modules)

/- Definition 6.27.1 (3): `pointInclusion x` is the canonical morphism from the one-point
ringed space carrying the stalk ring at `x` to `X`. -/
@[stacks 009A "the point inclusion as a morphism of ringed spaces"]
#check pointInclusion x

/- Definition 6.27.1 (4): the skyscraper module sheaf associated to `M` is its pushforward along
`pointInclusion x`; the shared owner records this as `RingedSpace.Module.Skyscraper.atPoint`. -/
@[stacks 009A "skyscraper sheaf of modules as pushforward from the point"]
#check RingedSpace.Module.Skyscraper.atPoint x M

/- Definition 6.27.1 (5): an `X.Modules` object is a skyscraper module sheaf when it is
isomorphic to `RingedSpace.Module.Skyscraper.atPoint x M` for some `x` and `M`. -/
@[stacks 009A "module sheaves isomorphic to a skyscraper module sheaf"]
#check RingedSpace.Module.IsSkyscraper ℱ

end AlgebraicGeometry
