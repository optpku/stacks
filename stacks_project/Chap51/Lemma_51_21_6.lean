module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor
import StacksCheckRecall

@[expose] public section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

/- Lemma 51.21.6: if `t` bounds the number of generators of an ideal `I` in a
Noetherian ring `A`, then the degree-`t + 1` Tor maps induced by sufficiently late
ideal-power quotient transitions vanish uniformly for every `A`-module. -/
@[stacks 0GA2] #check
  (CategoryTheory.DerivedCategory.IdealPower.torPowerMap_eq_zero_uniformly_of_generator_bound :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I : Ideal A) (t : ℕ)
      (h_generators : ∃ a : Fin t → I,
        I = Ideal.span (Set.range fun j ↦ (a j : A))),
      ∃ N c : ℕ, ∀ (M : ModuleCat.{u} A) (n : ℕ), N ≤ n →
        ((Tor (ModuleCat.{u} A) (t + 1)).obj M).map
          (ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))) = 0)

end CategoryTheory.DerivedCategory.IdealPower
