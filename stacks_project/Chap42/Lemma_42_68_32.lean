/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import StacksCheckRecall

universe u v

/- Lemma 42.68.32: for a regular element `a` on a finite dimension-one module `M`
over a Noetherian local ring `A`, `d_M(a, a)` is the parity sign of the length of
`M ⧸ a • ⊤`. -/
@[stacks 0AY9] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_same :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : A) (ha : IsSMulRegular M a) (hdim : Module.supportDim A M = 1),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant M a a ha ha hdim =
        (-1) ^ (Module.length A (QuotSMulTop a M)).toNat)
