/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Counterexamples.TwoClosedPoints.Sheaf
import StacksCheckRecall

/-!
# Example 6.29.2

The reusable construction is owned by
`TopCat.Counterexample.TwoClosedPoints`.  This source file records the textbook's
integer-valued specialization and its nine labelled conclusions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat.Counterexample.TwoClosedPoints
open TopCat.Counterexample.TwoClosedPoints.Tail

namespace Example_6_29_2

/- Example 6.29.2 (1): the stalk of the tail sheaf at `ξ_m` is zero when `m < n`. -/
@[stacks 009G "stage stalk vanishing before the tail begins"]
#check sheaf_stalk_generic_isZero (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (2): every generic-point stalk of the colimit tail sheaf is zero. -/
@[stacks 009G "zero stalks at the generic points"]
#check sheafColimit_stalk_generic_isZero (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (3): the eventual colimit of integer-valued tail products is nonzero. -/
@[stacks 009G "the eventual-sequence group is nonzero"]
#check eventualColimit_not_isZero_of_nontrivial (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (4): the first closed-point stalk of the colimit tail sheaf is the eventual
tail-product colimit. -/
@[stacks 009G "the first closed-point stalk is the eventual-sequence group"]
#check sheafColimit_stalk_first_isIsomorphic (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (5): the second closed-point stalk of the colimit tail sheaf is the eventual
tail-product colimit. -/
@[stacks 009G "the second closed-point stalk is the eventual-sequence group"]
#check sheafColimit_stalk_second_isIsomorphic (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (6): the colimit tail sheaf is the biproduct of the two skyscraper sheaves. -/
@[stacks 009G "identification with the two skyscraper summands"]
#check sheafColimit_isIsomorphic_skyscraperPair (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (7): global sections of the colimit tail sheaf are the binary biproduct of the
eventual colimit with itself. -/
@[stacks 009G "global sections of the colimit sheaf"]
#check sheafColimit_globalSections_isIsomorphic (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (8): the colimit of the stagewise global sections is the eventual tail-product
colimit. -/
@[stacks 009G "colimit of the stagewise global sections"]
#check globalSectionsColimit_isIsomorphic (AddCommGrpCat.of ℤ)

/- Example 6.29.2 (9): global sections do not preserve the filtered colimit of the integer-valued
tail sheaf system. -/
@[stacks 009G "failure of global sections to preserve this filtered colimit"]
#check globalSectionsComparison_not_isIso_of_nontrivial (AddCommGrpCat.of ℤ)

end Example_6_29_2
