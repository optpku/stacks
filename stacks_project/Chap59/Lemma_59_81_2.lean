module

public import ReasLib.RingTheory.Localization.Away.PolynomialPresentation
import StacksCheckRecall

@[expose] public section

open Polynomial

universe u

noncomputable section

/-- The source-facing coefficient map sends the localized variable to `Φ(s)`. -/
noncomputable def presentationBaseMap
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let G : Type u := Localization.Away (C π * X + 1)
    B →ₐ[A] G :=
  Localization.Away.PolynomialPresentation.baseMap π ℓ Φ hΦ_shape

section SourcePresentation

variable {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
  (Φ : Polynomial A) (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ)
  (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ)

/- Lemma 59.81.2 (1): the localization is presented by adjoining a root of
`Φ(s) - t` to the localization in which `π ^ ℓ t + 1` is inverted. -/
@[stacks 0GY3] #check
  (Localization.Away.PolynomialPresentation.equiv π ℓ hℓ.pos Φ hΦ_shape :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    Localization.Away (C π * X + 1) ≃ₐ[A]
      AdjoinRoot (Polynomial.map (algebraMap A B) Φ - C t))

/- The source presentation respects its specified coefficient map. -/
#check
  (Localization.Away.PolynomialPresentation.equiv_baseMap π ℓ hℓ.pos Φ hΦ_shape
      (algebraMap (Polynomial A) (Localization.Away (C (π ^ ℓ) * X + 1)) X) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    Localization.Away.PolynomialPresentation.equiv π ℓ hℓ.pos Φ hΦ_shape
        (Localization.Away.PolynomialPresentation.baseMap π ℓ Φ hΦ_shape
          (algebraMap (Polynomial A) B X)) =
      algebraMap B (AdjoinRoot p) (algebraMap (Polynomial A) B X))

/- Lemma 59.81.2 (2): the presented quotient has a power basis over the
localized coefficient algebra. -/
@[stacks 0GY3] #check
  (Localization.Away.PolynomialPresentation.powerBasis π ℓ hℓ.pos Φ hΦ_monic
      hΦ_degree :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    PowerBasis B (AdjoinRoot (Polynomial.map (algebraMap A B) Φ - C t)))

end SourcePresentation

end
