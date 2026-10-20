module

public import stacks_project.Chap59.Lemma_59_81_2
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Algebra.Defs
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed
public import ReasLib.RingTheory.Localization.Away.PolynomialPresentation.Surjectivity
import StacksCheckRecall

@[expose] public section

open Polynomial

universe u v

noncomputable section

/- Lemma 59.81.3: for an absolutely integrally closed `A`-algebra `R`, the
induced map from `G(R)` to `H(R)` is surjective, represented by precomposition
with the presentation map between their coordinate algebras. -/
@[stacks 0GY5] #check
  (Localization.Away.PolynomialPresentation.precomposition_surjective :
    ∀ {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
      [IsAbsolutelyIntegrallyClosed R] (π : A) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
      (Φ : Polynomial A) (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ)
      (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ),
      Function.Surjective
        (fun g : Localization.Away (C π * X + 1) →ₐ[A] R ↦
          g.comp (presentationBaseMap π ℓ Φ hΦ_shape)))
