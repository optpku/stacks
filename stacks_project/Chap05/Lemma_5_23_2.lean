/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConstructibleTopology.Spectral
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.2 (1): the constructible topology of a spectral space is
Hausdorff. -/
@[stacks 0901 "Hausdorffness"]
#check constructibleTopology_t2Space

/- Lemma 5.23.2 (2): the constructible topology of a spectral space is totally
disconnected. -/
@[stacks 0901 "total disconnectedness"]
#check constructibleTopology_totallyDisconnectedSpace

/- Lemma 5.23.2 (3): the constructible topology of a spectral space is
compact. -/
@[stacks 0901 "quasi-compactness"]
#check constructibleTopology_compactSpace
