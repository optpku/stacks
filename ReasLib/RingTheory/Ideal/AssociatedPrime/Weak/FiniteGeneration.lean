module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely generated weakly associated primes

This leaf compares exact, radical-based, and weak association when the prime
ideal is finitely generated, together with the corresponding Noetherian set
equalities.
-/

@[expose] public section

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Ideal.IsAssociatedToModule

/-- For a finitely generated ideal, exact-annihilator association is equivalent to weak
association. -/
@[stacks 058A "(1) finitely generated exact association"]
theorem iff_isWeaklyAssociatedToModule_of_fg
    (p : Ideal R) (hp : p.FG) :
    Ideal.IsAssociatedToModule R M p ↔
      Ideal.IsWeaklyAssociatedToModule R M p := sorry

end Ideal.IsAssociatedToModule

namespace IsAssociatedPrime

/-- For a finitely generated ideal, radical-based association is equivalent to weak
association. -/
@[stacks 058A "(1) finitely generated associated prime"]
theorem iff_isWeaklyAssociatedToModule_of_fg
    (p : Ideal R) (hp : p.FG) :
    IsAssociatedPrime p M ↔
      Ideal.IsWeaklyAssociatedToModule R M p := sorry

end IsAssociatedPrime

namespace associatedPrimes

/-- Over a Noetherian ring, radical-based and weakly associated prime sets
coincide. -/
@[stacks 058A "(2) Noetherian associated-prime equality"]
theorem eq_weaklyAssociatedPrimes_of_isNoetherianRing
    [IsNoetherianRing R] :
    associatedPrimes R M = weaklyAssociatedPrimes R M := sorry

end associatedPrimes

namespace associatedPrimesOfModule

/-- Over a Noetherian ring, exact-annihilator and weakly associated prime
sets coincide. -/
@[stacks 058A "(2) Noetherian exact associated-prime equality"]
theorem eq_weaklyAssociatedPrimes_of_isNoetherianRing
    [IsNoetherianRing R] :
    associatedPrimesOfModule R M = weaklyAssociatedPrimes R M := sorry

end associatedPrimesOfModule

end
