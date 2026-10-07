module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductBaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.33.5

The base-change compatibility of relative cup products is owned at the categorical level in
ReasLib.  This chapter entry only recalls that reusable statement.
-/

/- Lemma 21.33.5 (0H9A): relative cup products commute with canonical derived base-change maps
when the square and pullback-tensor comparisons are compatible. -/
@[stacks 0H9A]
#check @CategoryTheory.relativeDerivedCupProduct_baseChange_commSq
