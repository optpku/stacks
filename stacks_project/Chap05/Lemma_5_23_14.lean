/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Spectral.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.14: spectral spaces are exactly directed inverse limits of finite
`T₀` spaces, up to homeomorphism. -/
@[stacks 09XX]
#check SpectralSpace.iff_homeomorphic_directedLimit_finiteT0
