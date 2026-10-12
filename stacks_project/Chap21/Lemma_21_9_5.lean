/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Sections
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.5 (Tag 03F5): tensor the fixed-target free-abelian Cech complex with the ring
presheaf.  The root owner is presheaf-level; sectionwise evaluation remains a named companion. -/

@[stacks 03F5 "presheaf-level fixed-target tensor Cech complex"]
#check @CategoryTheory.Cech.FreeAbelian.tensorCoverComplex

@[stacks 03F5 "presheaf-level fixed-target tensor Cech homology vanishing"]
#check @CategoryTheory.Cech.FreeAbelian.tensorCoverComplex_homology_isZero_succ

#check @CategoryTheory.Cech.FreeAbelian.tensorCoverComplex_homology_isZero_of_pos
#check @CategoryTheory.Cech.FreeAbelian.Sectionwise.tensorChainComplex
