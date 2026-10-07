module

public import ReasLib.RingTheory.DividedPowers.Derivation
import StacksCheckRecall

@[expose] public section

universe u v w

/- Definition 60.6.1: for a ring map `f : A →+* B`, divided powers `δ` on an ideal
`J` of `B`, and a `B`-module `M`, a divided-power `A`-derivation consists of a
derivation `B → M` that vanishes on `f A` and satisfies the divided-power formula. -/
@[stacks 07HR] #check (DividedPowers.DividedPowerDerivation :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B] {J : Ideal B},
    (A →+* B) → DividedPowers J → (M : Type w) →
      [AddCommGroup M] → [Module B M] → Type (max v w))
