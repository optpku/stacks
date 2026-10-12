/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GenericFlatness.Locus.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Generic Flatness over a Reduced Base

The labeled statement retains the open dense set and its pointwise principal
neighborhoods.  The equivalent good-locus density form is recalled below.

@stack 051Z
-/

@[stacks 051Z "open dense locus with principal witnesses"]
#check @GenericFlatness.exists_open_dense_with_localizationCondition

/- The canonical reformulation takes `U` to be the good locus itself. -/
@[stacks 051Z "canonical good-locus density"]
#check @GenericFlatness.dense_of_finiteType_finiteModule_reduced
