module

public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.Interpolation
import StacksCheckRecall

@[expose] public section

open Polynomial

universe v

/- Lemma 59.81.4: with `A = AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)` and
`π = AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ) - 1`, the source sections
`σ₀` and `σ₁` are characterized by the localization coordinate having value
zero and one, respectively, modulo `I` and `J`. -/
@[stacks 0GY6]
#check
  (IsAbsolutelyIntegrallyClosed.existsCyclotomicInterpolationPoint :
    (ℓ : ℕ) → Nat.Prime ℓ → {R : Type v} → [CommRing R] →
      [Algebra (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) R] →
      [IsAbsolutelyIntegrallyClosed R] → (I J : Ideal R) → I + J = ⊤ →
        let A := AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)
        let π : A := AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ) - 1
        let B := Localization.Away (C π * X + 1)
        let coordinate : B := algebraMap (Polynomial A) B X
        ∃ point : B →ₐ[A] R,
          Ideal.Quotient.mk I (point coordinate) = 0 ∧
            Ideal.Quotient.mk J (point coordinate) = 1)

end
