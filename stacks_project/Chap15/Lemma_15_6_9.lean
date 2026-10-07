module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.FiniteProjective
import StacksCheckRecall

/-!
# Lemma 15.6.9

The source statement is the equivalence on finite-projective modules provided by the shared
surjective-pullback adjunction owner.

@stack 0D2J
-/

@[expose] public section

open CategoryTheory

universe u

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

@[stacks 0D2J "finite-projective pullback object property"]
#check (ModuleCat.Pullback.FiniteProjective.property S)

@[stacks 0D2J "finite-projective pullback category"]
#check (ModuleCat.Pullback.FiniteProjective.Category S)

@[stacks 0D2J "finite-projective pullback base-change functor"]
#check (ModuleCat.Pullback.FiniteProjective.baseChangeFunctor S)

@[stacks 0D2J "finite-projective pullback equivalence"]
#check (ModuleCat.Pullback.FiniteProjective.baseChangeFunctor_isEquivalence S)

#print axioms CategoryTheory.ModuleCat.Pullback.FiniteProjective.property
#print axioms CategoryTheory.ModuleCat.Pullback.FiniteProjective.Category
#print axioms CategoryTheory.ModuleCat.Pullback.FiniteProjective.baseChangeFunctor
