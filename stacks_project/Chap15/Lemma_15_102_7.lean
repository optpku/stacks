module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedAction

/-!
# Lemma 15.102.7

@stack 0928
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.IdealPower.Action
open CategoryTheory.ModuleCat.DerivedAction

universe u

/- Lemma 15.102.7 (0928): for a finite module over a Noetherian ring, a sufficiently deep
ideal-power inclusion factors through the derived tensor action of the ideal. -/
@[stacks 0928 "Lemma 15.102.7"]
#check @existsFactorization

#check fun {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] ↦
  existsFactorization I M

#check @idealAction
#check @derivedAction
#check @CategoryTheory.ModuleCat.DerivedAction.Complex.derivedAction
#check @CategoryTheory.ModuleCat.DerivedAction.Complex.derivedActionIso
