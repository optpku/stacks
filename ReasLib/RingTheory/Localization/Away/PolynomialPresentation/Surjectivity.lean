/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.PolynomialPresentation
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

namespace Localization.Away.PolynomialPresentation

open Polynomial

universe u v

noncomputable section

/-- Precomposition with the polynomial-localization presentation map is
surjective on points valued in an absolutely integrally closed algebra. -/
public theorem precomposition_surjective
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    [IsAbsolutelyIntegrallyClosed R] (π : A) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (Φ : Polynomial A) (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    Function.Surjective
      (fun g : Localization.Away (C π * X + 1) →ₐ[A] R ↦
        g.comp (baseMap π ℓ Φ hΦ_shape)) := sorry

end
end Localization.Away.PolynomialPresentation
