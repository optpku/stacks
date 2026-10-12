/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.DimensionOne.SimultaneousPowerFactorization

universe u

/- Lemma 42.4.4: a finite family of nonzerodivisors in a one-dimensional Noetherian
local ring, not all units, becomes unit multiples of powers of one nonzerodivisor in
each maximal localization of a suitable finite injective extension. The cokernel of the
extension is annihilated by a power of the maximal ideal. -/
@[stacks 0EAG] #check
  (IsLocalRing.existsFiniteExtensionWithLocalPowerFactorizations :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      ringKrullDim A = 1 → ∀ {r : ℕ}, 2 ≤ r → ∀ a : Fin r → A,
        (∀ i, a i ∈ nonZeroDivisors A) → (¬ ∀ i, IsUnit (a i)) →
          ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
              (_ : Function.Injective (algebraMap A B))
              (_ : Module.IsAnnihilatedByPower (IsLocalRing.maximalIdeal A)
                (B ⧸ (Algebra.linearMap A B).range)),
            ∀ (p : Ideal B) [p.IsMaximal],
              ∃ π : Localization.AtPrime p,
                π ∈ nonZeroDivisors (Localization.AtPrime p) ∧
                  ∀ i, ∃ (u : (Localization.AtPrime p)ˣ) (e : ℕ),
                    algebraMap B (Localization.AtPrime p) (algebraMap A B (a i)) =
                      (u : Localization.AtPrime p) * π ^ e)
