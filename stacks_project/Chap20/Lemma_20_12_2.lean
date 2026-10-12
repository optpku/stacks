/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.12.2 (09SX): injective module sheaves on a ringed space are flasque.  The
source-independent object property and its underlying-sheaf bridge live in `ReasLib`. -/

@[stacks 09SX]
#check @AlgebraicGeometry.RingedSpace.Modules.flasque_of_injective

@[stacks 09SX "underlying additive sheaf"]
#check @AlgebraicGeometry.RingedSpace.Modules.underlying_isFlasque_of_injective

#check @AlgebraicGeometry.RingedSpace.Modules.underlyingIsFlasque
