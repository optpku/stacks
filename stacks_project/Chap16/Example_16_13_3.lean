/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.Completion
import StacksCheckRecall

@[expose] public section

/- Example 16.13.3 (1): a Noetherian local ring has a unique canonical map
from its henselization to its maximal-ideal completion, and every map with
the canonical completion compatibility is injective. -/
@[stacks 0A1W]
#check @IsHenselizationOf.Completion.existsUnique_comparison
#check @IsHenselizationOf.Completion.map_bijective

@[stacks 0A1W]
#check @IsHenselizationOf.Completion.Comparison.injective

/- Example 16.13.3 (2): for a local domain which is a G-ring, the canonical
henselization image is the algebraic-closure subalgebra. -/
@[stacks 0A1W]
#check @IsHenselizationOf.Completion.Comparison.range_eq_of_isGRing
