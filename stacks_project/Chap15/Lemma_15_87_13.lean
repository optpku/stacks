/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Invariant
import StacksCheckRecall

/-!
# Lemma 15.87.13

@stack 091B
-/

@[expose] public section

/- Lemma 15.87.13: a morphism in the derived category of sequential inverse systems of abelian
groups induces an isomorphism on total right derived inverse limits when its canonical stagewise
sequential pro-morphism is invertible. This is the `AddCommGrpCat` specialization of the shared
derived sequential inverse-limit invariance theorem. -/
@[stacks 091B] #check @CategoryTheory.DerivedLimit.Pro.map_isIso

#check @CategoryTheory.DerivedLimit.Pro.isomorphisms
