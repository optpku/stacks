module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite fibre-product modules

Finiteness of the two components of a pullback-module triple implies finiteness of its explicit
fibre-product module over the surjective pullback ring.

@stack 0D2H
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Pullback

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- A pullback-module triple with finite components has a finite fibre-product module over the
pullback ring. -/
@[stacks 0D2H "finite fibre-product module"]
theorem rightAdjoint_finite (S : SurjectiveRingPullbackSituation B A A')
    (X : Pullback.Category S.toA S.fromAprime)
    (hfst : Module.Finite B X.fst) (hsnd : Module.Finite A' X.snd) :
    Module.Finite S.Bprime
      ((rightAdjoint S.bprimeToB S.bprimeToAprime S.comm).obj X) := sorry

end CategoryTheory.ModuleCat.Pullback
