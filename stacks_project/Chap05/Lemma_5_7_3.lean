/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConnectedComponents.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.3

Mathlib owns the closure and closedness facts; `ReasLib.Topology.ConnectedComponents.Basic`
owns the maximal-component bridges.
-/

/- Lemma 5.7.3 (1): closures of connected subsets are connected. -/
@[stacks 004T "closures of connected subsets are connected"]
#check @IsConnected.closure

/- Lemma 5.7.3 (2): connected components are closed. -/
@[stacks 004T "connected components are closed"]
#check @isClosed_connectedComponent

/- Lemma 5.7.3 (3): a connected subset lies in a unique maximal connected subset. -/
@[stacks 004T "connected subsets lie in unique connected components"]
#check @IsConnected.existsUnique_maximalSuperset

/- Lemma 5.7.3 (4): every point lies in a unique maximal connected subset. -/
@[stacks 004T "every point lies in a unique connected component"]
#check @existsUnique_maximal_isConnected_containing
