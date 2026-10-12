/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Jacobson.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.7 (1): the closed-point trace is a bijection on finite unions of
locally closed subsets in a Jacobson space. -/
@[stacks 005Z "bijection on finite unions of locally closed subsets"]
#check JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_bijOn

/- The same correspondence is available as an equivalence of the canonical
subtypes, whose inverse is specified by its closed-point trace. -/
@[stacks 005Z "subtype equivalence for finite-locally-closed traces"]
#check @JacobsonSpace.ClosedPoints.finiteUnionTraceEquiv

/- Lemma 5.18.7 (2): the finite-locally-closed closed-point trace preserves and
reflects inclusion. -/
@[stacks 005Z "inclusion-preserving correspondence"]
#check @IsFiniteUnionOfLocallyClosed.closedPointsTrace_subset_iff

/- Lemma 5.18.7 (3): the finite-locally-closed closed-point trace preserves and
reflects local closedness. -/
@[stacks 005Z "preservation of locally closed subsets"]
#check @IsFiniteUnionOfLocallyClosed.isLocallyClosed_iff_closedPointsTrace

/- Lemma 5.18.7 (4): the finite-locally-closed closed-point trace preserves and
reflects openness. -/
@[stacks 005Z "preservation of open subsets"]
#check @IsFiniteUnionOfLocallyClosed.isOpen_iff_closedPointsTrace

/- Lemma 5.18.7 (5): the finite-locally-closed closed-point trace preserves and
reflects closedness. -/
@[stacks 005Z "preservation of closed subsets"]
#check @IsFiniteUnionOfLocallyClosed.isClosed_iff_closedPointsTrace
