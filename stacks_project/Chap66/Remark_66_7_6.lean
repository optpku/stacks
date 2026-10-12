/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Remark_66_7_6_Instances
public import stacks_project.Chap66.Remark_66_7_6_LocalRing
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- If `P` is a property of local rings invariant under étale ring maps at corresponding
primes, then `𝒫(U, u) := P(𝒪_{U, u})` is an étale-local property of scheme germs. In
this situation, “the local ring of `X` at `x` has `P`” means `X` has this germ property
at `x`. -/
@[stacks 0BBL] #check
  (GermProperty.ofLocalRing.isEtaleLocal :
    ∀ {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop},
      IsEtaleLocalAtPrimes P → (GermProperty.ofLocalRing P).IsEtaleLocal)
@[stacks 0BBL] #check AlgebraicSpace.localRingHas

/- Remark 66.7.6 (1): Noetherianity of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (isNoetherianRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsNoetherianRing R)

/- Remark 66.7.6 (2): having Krull dimension `d` is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (ringKrullDim_isEtaleLocalAtPrimes :
    ∀ d : WithBot ℕ∞, IsEtaleLocalAtPrimes fun R ↦ ringKrullDim R = d)

/- Remark 66.7.6 (3): regularity of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (isRegularLocalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsRegularLocalRing R)

/- Remark 66.7.6 (4): being a discrete valuation ring is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (isDiscreteValuationRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes isDiscreteValuationLocalRing)

/- Remark 66.7.6 (5): reducedness of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (isReduced_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ _root_.IsReduced R)

/- Remark 66.7.6 (6): normality of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (isNormalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsNormalRing R)

/- Remark 66.7.6 (7): being Noetherian of depth `k` is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (isNoetherianOfDepth_isEtaleLocalAtPrimes :
    ∀ k : ℕ, IsEtaleLocalAtPrimes (isNoetherianOfDepth k))

/- Remark 66.7.6 (8): being Noetherian and Cohen–Macaulay is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (isNoetherianCohenMacaulay_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes isNoetherianCohenMacaulay)

/- Remark 66.7.6 (9): being Noetherian and Gorenstein is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (isGorensteinLocalRing_isEtaleLocalAtPrimes :
    IsEtaleLocalAtPrimes fun R ↦ IsGorensteinLocalRing R)
