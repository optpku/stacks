module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Point.CounitSplit

/-!
# Canonical recall for Lemma 7.32.9

The source statement is a specialization of the general counit-section API
for adjunctions into `Type`; the topos-point bridge lives in ReasLib so that
later chapters can import it without depending on Chapter 7.
-/

@[expose] public section

open CategoryTheory

/- Lemma 7.32.9 (05UX): for a topos point, the counit
`p^{-1}(p_* E) ⟶ E` has the canonical section
`p.typeCounitSection.app E`. The source-tagged specialization is
`MorphismOfTopoiIn.typeCounitSection_leftInverse`. -/

#check @Adjunction.counitSection
#check @Adjunction.counitSection_comp
#check @Adjunction.counit_leftInverse
#check @Adjunction.counit_isSplitEpi
#check @Adjunction.reflectsMonomorphisms_of_preservesTerminal
#check @Adjunction.reflectsEpimorphisms_of_preservesTerminal
#check @MorphismOfTopoiIn.typeCounitSection
@[stacks 05UX] #check @MorphismOfTopoiIn.typeCounitSection_leftInverse
#check @MorphismOfTopoiIn.typeCounit_isSplitEpi
