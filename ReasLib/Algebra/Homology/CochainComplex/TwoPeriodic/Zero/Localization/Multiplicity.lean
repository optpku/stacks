/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.EulerCharacteristic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization.Multiplicity
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Localization.Determinant
public import ReasLib.RingTheory.Module.Support.FiniteLength

/-!
# Multiplicity from localized determinants of module endomorphisms

This file expresses the difference between the cokernel and kernel lengths of a module
endomorphism as a sum of orders of its localized determinant units.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- For a finite module endomorphism with finite-length kernel and cokernel and support dimension
at most one, the cokernel length minus the kernel length is the sum of the orders of its localized
determinant units at the enumerated nonclosed support primes. -/
theorem cokernelLength_sub_kernelLength_eq_sum
    (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
    (hdim : Module.supportDim R M ≤ 1) {t : ℕ}
    (q : Fin t → PrimeSpectrum R) (hq_injective : Function.Injective q)
    (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint R)
    (hsupport : Module.support R M =
      Set.insert (IsLocalRing.closedPoint R) (Set.range q)) :
    ((Module.length R (cokernel ψ : ModuleCat R)).toNat : ℤ) -
        ((Module.length R (kernel ψ : ModuleCat R)).toNat : ℤ) =
      ∑ i, ofZeroDeterminantOrderAt M ψ hCoker hKer hdim (q i)
        (hsupport.symm ▸ Set.mem_insert_of_mem (IsLocalRing.closedPoint R) ⟨i, rfl⟩)
        (hq_ne_closedPoint i) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
