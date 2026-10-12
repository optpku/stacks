/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Polynomial.Origin
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.17.3: if `(R, m)` is a Noetherian local ring and `n ≥ 1`, then in
`MvPolynomial (Fin n) R` the origin ideal `m' = spanMapCX (Fin n) (maximalIdeal R)`
(equivalently `(m, x₁, …, xₙ)`) satisfies
`ringKrullDim (Localization.AtPrime m') = ringKrullDim R + n`.
The identity also holds for `n = 0`. -/
@[stacks 02LU] #check (MvPolynomial.ringKrullDim_localizationAtPrime_spanMapCX :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ),
    ringKrullDim (Localization.AtPrime
      (MvPolynomial.spanMapCX (Fin n) (IsLocalRing.maximalIdeal R))) = ringKrullDim R + n)
