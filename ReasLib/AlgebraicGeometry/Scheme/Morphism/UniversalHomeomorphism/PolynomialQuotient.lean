/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Universal homeomorphisms from polynomial quotients

This module records universal homeomorphisms of affine schemes arising from a cusp
presentation and from a prime-power presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CuspQuotient

/-- For a cusp relation `x ^ 3 = y ^ 2`, the affine spectrum morphism associated to
`A → A[t] / (t ^ 2 - x, t ^ 3 - y)` induces isomorphisms on all residue fields. -/
theorem residueFieldMap_isIso
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
    ∀ z : Spec (.of B), IsIso (f.residueFieldMap z) := sorry

/-- For a cusp relation `x ^ 3 = y ^ 2`, the affine spectrum morphism associated to
`A → A[t] / (t ^ 2 - x, t ^ 3 - y)` is a universal homeomorphism. -/
theorem universalHomeomorphism
    (A : Type u) [CommRing A] (x y : A) (hxy : x ^ 3 = y ^ 2) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
      Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom φ)) := sorry

end CuspQuotient

namespace PrimePowerQuotient

/-- For a prime `p` and a relation `(p : A) ^ p * x = y ^ p`, the affine spectrum
morphism associated to `A → A[t] / (t ^ p - x, p * t - y)` is a universal homeomorphism. -/
theorem universalHomeomorphism
    (A : Type u) [CommRing A] (x y : A) (p : ℕ) (hp : Nat.Prime p)
    (hxy : (p : A) ^ p * x = y ^ p) :
    let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y} : Set (Polynomial A))
    let B : Type u := Polynomial A ⧸ I
    let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom φ)) := sorry

end PrimePowerQuotient

end AlgebraicGeometry
