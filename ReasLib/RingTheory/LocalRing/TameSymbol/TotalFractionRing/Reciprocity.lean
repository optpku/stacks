module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing.HeightOne

@[expose] public section

/-!
# Reciprocity for integral tame symbols at height-one primes

This module records the global vanishing of the finitely supported sum of local
integral tame-symbol orders.
-/

noncomputable section

open scoped BigOperators nonZeroDivisors

universe u

namespace TameSymbol.Total

/-- The sum of the local integral tame-symbol orders over all height-one primes of a
two-dimensional Noetherian local ring vanishes. -/
theorem finsum_orderAt_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (a b : A⁰) :
    ∑ᶠ p : PrimeSpectrum.HeightOne A, orderAt A hdim p a b = 0 := sorry

end TameSymbol.Total
