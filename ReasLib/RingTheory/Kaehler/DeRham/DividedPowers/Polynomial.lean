/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.RingTheory.DividedPowers.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct

universe u v

namespace KaehlerDifferential.DeRham

/-- Adjoining an ordinary polynomial variable decomposes divided-power differentials into the
base-changed differential module and the polynomial generator summand. -/
theorem dividedPowerDifferential_polynomial
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J)
    (δx : DividedPowers (J.map (algebraMap B (Polynomial B))))
    (hδx : DividedPowers.IsDPMorphism δ δx (algebraMap B (Polynomial B))) :
    Nonempty (dividedPowerDifferential ((algebraMap B (Polynomial B)).comp f) δx ≃ₗ[Polynomial B]
      ((Polynomial B ⊗[B] dividedPowerDifferential f δ) × Polynomial B)) := sorry

/-- Adjoining one divided-power polynomial variable gives the analogous decomposition with the
canonical finite divided-power polynomial algebra. -/
theorem dividedPowerDifferential_dpPolynomial
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J) :
    Nonempty (dividedPowerDifferential
      ((algebraMap B (DPPolynomial.Finite.Ring B 1)).comp f)
      (DPPolynomial.Finite.dividedPowers δ) ≃ₗ[DPPolynomial.Finite.Ring B 1]
      ((DPPolynomial.Finite.Ring B 1 ⊗[B] dividedPowerDifferential f δ) ×
        DPPolynomial.Finite.Ring B 1)) := sorry

end KaehlerDifferential.DeRham
