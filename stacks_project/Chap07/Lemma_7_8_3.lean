/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Lemma 7.8.3

Fixed-target family relations are reusable site infrastructure, so their
definitions and relation laws are owned by ReasLib.  This file retains the
five source-facing clauses as tagged recalls.
-/

@[expose] public section

/- Lemma 7.8.3 (00VV) (1): equality of generated presieves gives
tautological equivalence of the two families. -/
@[stacks 00VV "(1)"] #check @CategoryTheory.SemiRepresentableFamily.Over.CombinatoriallyEquivalent.toTautologicallyEquivalent

/- Lemma 7.8.3 (00VV) (2): tautologically equivalent families refine one
another. -/
@[stacks 00VV "(2)"] #check @CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent.mutuallyRefines

/- Lemma 7.8.3 (00VV) (3): combinatorial equivalence is an equivalence
relation. -/
@[stacks 00VV "(3)"] #check @CategoryTheory.SemiRepresentableFamily.Over.CombinatoriallyEquivalent.isEquivalence

/- Lemma 7.8.3 (00VV) (4): tautological equivalence is an equivalence
relation. -/
@[stacks 00VV "(4)"] #check @CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent.isEquivalence

/- Lemma 7.8.3 (00VV) (5): mutual refinement is an equivalence relation. -/
@[stacks 00VV "(5)"] #check @CategoryTheory.SemiRepresentableFamily.Over.MutuallyRefines.isEquivalence
