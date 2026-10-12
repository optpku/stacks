/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.BoundedAbove
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.8 (09V8): local upper boundedness and pseudo-coherent cohomology imply
`m`-pseudo-coherence. -/
@[stacks 09V8]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedAbove.isMPseudoCoherent

-- The source's globally bounded-above parenthetical case is a canonical specialization.
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isMPseudoCoherent_of_isLE
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isLocallyBoundedAbove_of_isLE
