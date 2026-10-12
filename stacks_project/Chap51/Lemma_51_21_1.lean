/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor
import StacksCheckRecall

@[expose] public section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

/- Lemma 51.21.1: in every positive Tor degree, a fixed power-annihilation bound gives a
uniform cutoff for the maps induced by ideal-power quotient transitions. -/
@[stacks 0G9X] #check
  (CategoryTheory.DerivedCategory.IdealPower.torPowerMap_eq_zero_uniformly_of_pow_le_annihilator :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I : Ideal A) (m i : ℕ), 0 < i →
      ∃ c : ℕ, ∀ M : ModuleCat.{u} A, I ^ m ≤ Module.annihilator A M →
        ∀ n : ℕ, c ≤ n →
          ((Tor (ModuleCat.{u} A) i).obj M).map
            (ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))) = 0)

end CategoryTheory.DerivedCategory.IdealPower
