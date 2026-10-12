/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Product
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

variable {ι : Type u} [Fintype ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)]

/- Lemma 46.3.19: for a finite product of rings, adequate module-valued functors correspond to
families of adequate module-valued functors over the factors. -/
@[stacks 06VB] #check
  (ModuleValuedFunctor.adequateFunctorPiIsEquivalence (A := A) :
    (ModuleValuedFunctor.adequateFunctorPi A).IsEquivalence)
