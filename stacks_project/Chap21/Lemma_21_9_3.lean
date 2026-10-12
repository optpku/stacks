/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.9.3 (Tag 03AS): fixed-target free-abelian Cech comparison.  The ReasLib owner keeps
the family in `Over U`, so the intersections are fibre products over the displayed target. -/

@[stacks 03AS "fixed-target free-abelian Cech cover complex"]
#check @CategoryTheory.Cech.FreeAbelian.coverComplex

@[stacks 03AS "fixed-target Hom-to-Cech cochain functor"]
#check @CategoryTheory.Cech.FreeAbelian.homFunctor

@[stacks 03AS "fixed-target degreewise Hom-to-Cech comparison"]
#check @CategoryTheory.Cech.FreeAbelian.degreeComparison

@[stacks 03AS "fixed-target degreewise comparison is an isomorphism"]
#check @CategoryTheory.Cech.FreeAbelian.degreeComparison_isIso

@[stacks 03AS "fixed-target natural Hom-to-Cech comparison"]
#check @CategoryTheory.Cech.FreeAbelian.comparison

@[stacks 03AS "fixed-target natural comparison is an isomorphism"]
#check @CategoryTheory.Cech.FreeAbelian.comparison_isIso
