/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

/- The ordinary sheaf clauses are exactly the generic stalk–skyscraper adjunction, whose
coefficient category may be `Type u`, `AddCommGrpCat`, or another algebraic category with the
required colimits. For module sheaves the coefficient ring varies with the open set, so the
source formula is recovered instead from the point inclusion of Definition 6.27.1, the canonical
pullback–pushforward adjunction, and the stalk comparison of Lemma 6.26.4. This keeps the generic
owner visible while avoiding a second construction of the one-point ringed space. -/

/- Lemma 6.27.3 (1): for sheaves of sets, abelian groups, or algebraic structures, taking the
stalk at `x` is left adjoint to the skyscraper-sheaf functor at `x`. -/
@[stacks 009C "stalk and skyscraper adjunction for ordinary sheaves"]
recall TopCat.Sheaf.Skyscraper.stalkAdjunction

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}} (x : X)
variable (ℱ : X.Modules)
variable (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))

/- Lemma 6.27.3 (2): in the canonical point-pullback model of the module stalk, morphisms from
the stalk of `ℱ` at `x` to `M` are naturally equivalent to morphisms from `ℱ` to the skyscraper
module sheaf attached to `M`. The shared owner
`RingedSpace.Module.Skyscraper.adjunction` hides the one-point evaluation and
restriction-of-scalars implementation from consumers. -/
@[stacks 009C "stalk-module and skyscraper-module Hom equivalence"]
#check (RingedSpace.Module.Skyscraper.adjunction x).homEquiv ℱ M

/- Companion bridge: the unique stalk of `pointRingedSpace x` is canonically the original stalk
ring, without exposing a choice of decidable membership on the one-point space. -/
#check PointRingedSpace.stalkIso x

/- Companion bridge: Lemma 6.26.4 identifies the pullback appearing above, at the unique point,
with the scalar extension of the source-facing stalk module. This is an implementation boundary
for the module clause, not an additional source assertion. -/
#check RingedSpace.Hom.pullbackStalkIso (pointInclusion x) ℱ PUnit.unit

end

end AlgebraicGeometry
