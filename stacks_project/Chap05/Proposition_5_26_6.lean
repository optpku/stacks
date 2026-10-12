/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ExtremallyDisconnected.Projective
import StacksCheckRecall

@[expose] public section

/- Proposition 5.26.6: extremal disconnectedness, splitting of compact Hausdorff surjections,
and compact-Hausdorff projectivity are equivalent. -/
@[stacks 08YN]
#check CompactT2.extremallyDisconnected_section_projective_tfae
