/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.3: derived pullback preserves `m`-pseudo-coherence.  The ringed-space statement is
a thin specialization of the reusable bundled ringed-site owner. -/

@[stacks 09U7]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.pullback

-- The more general ringed-site theorem is available without a Chapter 21 import.
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.pullback

