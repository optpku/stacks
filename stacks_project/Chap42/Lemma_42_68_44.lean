/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Localization.Multiplicity
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

universe u v

/- Lemma 42.68.44: for a finite module endomorphism over a Noetherian local ring whose kernel
and cokernel have finite length and whose support has dimension at most one, the cokernel length
minus the kernel length is the sum of the orders of its localized determinant units at the
enumerated nonclosed support primes. -/
@[stacks 02QE] #check
  (CategoryTheory.TwoPeriodicEndomorphism.cokernelLength_sub_kernelLength_eq_sum :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (M : ModuleCat.{v} R) [Module.Finite R M] (ψ : M ⟶ M)
      (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
      (hKer : IsFiniteLength R (kernel ψ : ModuleCat R))
      (hdim : Module.supportDim R M ≤ 1) {t : ℕ}
      (q : Fin t → PrimeSpectrum R) (hq_injective : Function.Injective q)
      (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint R)
      (hsupport : Module.support R M =
        Set.insert (IsLocalRing.closedPoint R) (Set.range q)),
      ((Module.length R (cokernel ψ : ModuleCat R)).toNat : ℤ) -
          ((Module.length R (kernel ψ : ModuleCat R)).toNat : ℤ) =
        ∑ i, CategoryTheory.TwoPeriodicEndomorphism.ofZeroDeterminantOrderAt
          M ψ hCoker hKer hdim (q i)
          (hsupport.symm ▸ Set.mem_insert_of_mem (IsLocalRing.closedPoint R) ⟨i, rfl⟩)
          (hq_ne_closedPoint i))
