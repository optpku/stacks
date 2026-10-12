/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Open
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.11.2

The reusable open-restriction API for irreducible closed subsets is owned by
`ReasLib.Topology.IrreducibleCloseds.Open`.
-/

/- Lemma 5.11.2: codimension is unchanged by restricting an irreducible closed subset to an
open subspace which it meets. -/
@[stacks 02I4]
#check @coheight_eq_restrictOpen
