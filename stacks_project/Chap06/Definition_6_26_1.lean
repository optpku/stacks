/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- Mathlib's canonical `SheafOfModules.pushforward` and `SheafOfModules.pullback` are site-generic,
while the reusable `RingedSpace.Hom` API owns their specialization to a morphism of ringed spaces, together
with the structure-sheaf comparison maps and the stalk-module model used downstream. The numbered
item therefore records the two source constructions without remaining the infrastructure owner. -/

/- Definition 6.26.1 (1): the pushforward of an `X.Modules` object along a morphism of ringed
spaces `f : X ⟶ Y` is the canonical direct-image functor
`f_* : X.Modules ⥤ Y.Modules`, obtained by restricting scalars along the structure-sheaf
morphism `toRingCatSheafHom f`. -/
@[stacks 0095 "pushforward of module sheaves on ringed spaces"]
recall pushforward

/- Definition 6.26.1 (2): the pullback of a `Y.Modules` object along a morphism of ringed spaces
`f : X ⟶ Y` is the canonical inverse-image functor `f^* : Y.Modules ⥤ X.Modules`, owned by
`SheafOfModules.pullback (toRingCatSheafHom f)`. -/
@[stacks 0095 "pullback of module sheaves on ringed spaces"]
recall pullback

end RingedSpace.Hom

end AlgebraicGeometry
