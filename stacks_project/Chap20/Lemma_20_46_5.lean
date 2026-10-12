/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract.Lifting
import StacksCheckRecall

@[expose] public section

/- Lemma 20.46.5: a morphism from a finite-free retract `𝒪_X`-module locally lifts through an
epimorphism.  The ReasLib owner separates the restriction-level predicate, the point-neighborhood
view, and the open-cover view; it also exposes the more general locally finite-free-retract
source theorem. -/

@[stacks 08C6 "point-neighborhood view"]
#check @AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract.at_of_property

@[stacks 08C6 "open-cover view"]
#check @AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract.cover_of_property

#check @AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract.at_of_isLocal
#check @AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract.cover_of_isLocal
#check @AlgebraicGeometry.RingedSpace.Modules.IsLiftableOn
#check @AlgebraicGeometry.RingedSpace.Modules.IsLocallyLiftableAt
