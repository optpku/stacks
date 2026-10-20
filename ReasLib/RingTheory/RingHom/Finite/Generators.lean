/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators

universe u v

namespace RingHom

/-- A homomorphism of commutative rings is finite exactly when a finite family spans the target
using coefficients mapped from the source. -/
theorem finite_iff_exists_generators {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    φ.Finite ↔ ∃ (n : ℕ) (generators : Fin n → B),
      ∀ value : B, ∃ coefficients : Fin n → A,
        value = ∑ index, φ (coefficients index) * generators index := sorry

end RingHom
