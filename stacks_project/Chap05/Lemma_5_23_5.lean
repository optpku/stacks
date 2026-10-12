/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Spectral.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.5: a constructibly closed subspace of a spectral space is
spectral. -/
@[stacks 0902]
#check IsClosed.spectralSpace_subtype_of_constructibleTopology
