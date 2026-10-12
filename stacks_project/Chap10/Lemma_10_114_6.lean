/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
import StacksCheckRecall

@[expose] public section

/-!
# Local Dimension at a Closed Point

@stack 00OU
-/

/- Lemma 10.114.6 (Stacks tag `00OU`): if `m : MaximalSpectrum S` is a closed
point of a finite-type affine spectrum over a field, its local topological Krull
dimension equals `ringKrullDim (Localization.AtPrime m.asIdeal)`. -/
@[stacks 00OU]
#check @MaximalSpectrum.topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime
