/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed
public import ReasLib.RingTheory.AdjoinRoot.Unit

@[expose] public section

open Polynomial

universe u v

namespace IsAbsolutelyIntegrallyClosed

noncomputable section

/-- A finite-order localization coordinate admits a point with prescribed values
at two comaximal ideals in an absolutely integrally closed algebra. -/
theorem existsInterpolationPoint
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    [IsAbsolutelyIntegrallyClosed R] (π : A)
    (hπ_root : IsOfFinOrder (π + 1)) (I J : Ideal R) (hIJ : I + J = ⊤) :
    let B := Localization.Away (C π * X + 1)
    let coordinate : B := algebraMap (Polynomial A) B X
    ∃ point : B →ₐ[A] R,
      Ideal.Quotient.mk I (point coordinate) = 0 ∧
        Ideal.Quotient.mk J (point coordinate) = 1 := sorry

/-- For a prime cyclotomic root, the localization coordinate has a point with
the canonical values zero and one modulo any two comaximal ideals. -/
theorem existsCyclotomicInterpolationPoint
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {R : Type v} [CommRing R]
    [Algebra (AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)) R]
    [IsAbsolutelyIntegrallyClosed R] (I J : Ideal R) (hIJ : I + J = ⊤) :
    let A := AdjoinRoot (Polynomial.cyclotomic ℓ ℤ)
    let π : A := AdjoinRoot.root (Polynomial.cyclotomic ℓ ℤ) - 1
    let B := Localization.Away (C π * X + 1)
    let coordinate : B := algebraMap (Polynomial A) B X
    ∃ point : B →ₐ[A] R,
      Ideal.Quotient.mk I (point coordinate) = 0 ∧
        Ideal.Quotient.mk J (point coordinate) = 1 := sorry

end

end IsAbsolutelyIntegrallyClosed

end
