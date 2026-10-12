/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
import StacksCheckRecall

/-!
# Lemma 15.6.6

The source statement is the surjectivity theorem for the shared fibre-product right adjoint.

@stack 08KJ
-/

@[expose] public section

open CategoryTheory

universe u


variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/- Lemma 15.6.6: componentwise surjective morphisms of pullback-module triples induce a
surjective morphism on fibre-product modules. -/
@[stacks 08KJ "fibre-product module surjectivity"]
#check (ModuleCat.Pullback.map_surjective S)

@[stacks 08KJ "canonical fibre-product module functor"]
#check (ModuleCat.Pullback.rightAdjoint S.bprimeToB S.bprimeToAprime S.comm)
