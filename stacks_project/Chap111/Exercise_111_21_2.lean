/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.ClosedFiberDimension
import StacksCheckRecall

/-!
# Exercise 111.21.2

Closed-fiber Krull dimension bounds for injective finite-type domain extensions of
the polynomial ring `MvPolynomial (Fin n) k`.
-/

@[expose] public section

universe u v

/- Exercise 111.21.2 (1): if `k` is algebraically closed, `n ≥ 1`, and
`algebraMap (MvPolynomial (Fin n) k) A` is an injective finite-type extension of domains,
writing `d = ringKrullDim A` and `m = idealOfVars (Fin n) k`, one has
`d - 1 ≥ ringKrullDim (A ⧸ mA) ≥ d - n` whenever `A ⧸ mA ≠ 0`. -/
@[stacks 0CVS] #check
  (MvPolynomial.ringKrullDim_map_idealOfVars_bounds :
    ∀ {k : Type u} {A : Type v} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
      {n : ℕ} [NeZero n] [Algebra (MvPolynomial (Fin n) k) A]
      [Algebra.FiniteType (MvPolynomial (Fin n) k) A]
      (hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) k) A))
      (hne : Ideal.map (algebraMap (MvPolynomial (Fin n) k) A) (MvPolynomial.idealOfVars (Fin n) k) ≠ ⊤),
      ringKrullDim
          (A ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) k) A)
            (MvPolynomial.idealOfVars (Fin n) k)) + 1 ≤
        ringKrullDim A ∧
      ringKrullDim A ≤
        ringKrullDim
            (A ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) k) A)
              (MvPolynomial.idealOfVars (Fin n) k)) + n)

/- Exercise 111.21.2 (2): for each `r < n`, the closed fiber of `fiberDimHom k n r` has
Krull dimension `r`, so every integer in the range of the bounds occurs. -/
@[stacks 0CVS] #check
  (MvPolynomial.ringKrullDim_map_fiberDimHom :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ} [NeZero n], r < n →
      ringKrullDim
          (MvPolynomial (Fin n) k ⧸
            Ideal.map (MvPolynomial.fiberDimHom k n r) (MvPolynomial.idealOfVars (Fin n) k)) = r)

/- Exercise 111.21.2 (3): the closed fiber of `unequalComponentsHom` has irreducible components
of unequal Krull dimension. -/
@[stacks 0CVS] #check
  (MvPolynomial.ringKrullDim_planePrime_ne_linePrime :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      MvPolynomial.planePrime k ∈
          (Ideal.map (MvPolynomial.unequalComponentsHom k)
            (MvPolynomial.idealOfVars (Fin 2) k)).minimalPrimes ∧
      MvPolynomial.linePrime k ∈
          (Ideal.map (MvPolynomial.unequalComponentsHom k)
            (MvPolynomial.idealOfVars (Fin 2) k)).minimalPrimes ∧
      ringKrullDim (MvPolynomial (Fin 3) k ⧸ MvPolynomial.planePrime k) ≠
        ringKrullDim (MvPolynomial (Fin 3) k ⧸ MvPolynomial.linePrime k))
