/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 47.3.2: restriction of scalars along a flat commutative ring map sends every injective
target-ring module to an injective source-ring module. Applying the checked preservation property
to an injective `E : ModuleCat S` gives the stated objectwise conclusion. -/
@[stacks 08XQ] #check
  (ModuleCat.RestrictScalars.preservesInjectiveObjects_of_flat :
    ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), f.Flat →
      (ModuleCat.restrictScalars.{u} f).PreservesInjectiveObjects)
