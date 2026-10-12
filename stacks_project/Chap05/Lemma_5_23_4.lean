/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConstructibleTopology.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.4: a continuous map of spectral spaces is spectral exactly when
it is constructible-topology continuous. -/
@[stacks 0G1J]
#check Continuous.isSpectralMap_iff_constructibleTopology
