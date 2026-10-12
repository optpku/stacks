/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.Induced.Isomorphism
import StacksCheckRecall

/-!
# Lemma 15.87.4

@stack 0H9K
-/

@[expose] public section

/-
Lemma 15.87.4 (Stacks 0H9K): a morphism of pro-systems of abelian groups induces maps on
`lim` and `R¹ lim`, and a pro-isomorphism induces isomorphisms on both.  The shared owner uses
`Pro.SequentialHom` for representative data, `DerivedLimit.R1` for the first derived limit, and
the common-refinement quotient for representative-independent maps; `quotientToHom` compares
that quotient with actual morphisms of pro-objects.
-/

@[stacks 0H9K] #check @CategoryTheory.Pro.SequentialHom.Quotient.maps_isIso
#check @CategoryTheory.Pro.SequentialHom.Quotient.limitMap
#check @CategoryTheory.Pro.SequentialHom.Quotient.firstDerivedLimitMap
#check @CategoryTheory.Pro.SequentialHom.limitMap
#check @CategoryTheory.Pro.SequentialHom.firstProductMap
#check @CategoryTheory.Pro.SequentialHom.secondProductMap
#check @CategoryTheory.Pro.SequentialHom.firstDerivedLimitMap
#check @CategoryTheory.Pro.SequentialHom.milnorDifferenceCommSq
