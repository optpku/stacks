/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

@[expose] public section

universe u v w

open MvPolynomial

namespace Algebra.SquarePresentation

/-- The naive pre-submersive presentation of a quotient of `R[x₁,…,xₙ]` by
`n` polynomials. -/
noncomputable def naive {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) :
    PreSubmersivePresentation R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin n) :=
  PreSubmersivePresentation.naive (fun i : Fin n ↦ i) Function.injective_id

/-- The Jacobian of a square polynomial presentation is the class of
`det (∂fᵢ / ∂xⱼ)` in the quotient algebra. -/
theorem jacobian_eq_det {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) :
    (naive n f).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range f))
        (Matrix.det fun i j : Fin n ↦ pderiv j (f i)) :=
  sorry

/-- The submersive presentation associated to a square polynomial presentation
whose Jacobian is a unit in the quotient algebra. -/
noncomputable def submersive {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) (hjac : IsUnit (naive n f).jacobian) :
    SubmersivePresentation R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin n) where
  toPreSubmersivePresentation := naive n f
  jacobian_isUnit := hjac

/-- A submersive presentation with equally many variables and relations has
relative dimension zero. -/
theorem submersive_dimension {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) (hjac : IsUnit (naive n f).jacobian) :
    (submersive n f hjac).dimension = 0 :=
  sorry

/-- For a square polynomial presentation, the Jacobian is a unit if and only if
the module of relative Kähler differentials is subsingleton. -/
theorem isUnit_jacobian_iff_subsingleton_kaehlerDifferential
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R) :
    IsUnit (naive n f).jacobian ↔
      Subsingleton Ω[(MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))⁄R] :=
  sorry

/-- Every map out of a square polynomial quotient with unit Jacobian lifts uniquely
through a surjective algebra homomorphism whose kernel has square zero. -/
theorem existsUnique_lift
    {R : Type u} {B' : Type v} {B : Type w} [CommRing R] [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R)
    (hjac : IsUnit (naive n f).jacobian) (π : B' →ₐ[R] B)
    (hπ : Function.Surjective π) (hker : (RingHom.ker π) ^ 2 = ⊥)
    (φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B) :
    ∃! φ' : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B',
      π.comp φ' = φ :=
  sorry

end Algebra.SquarePresentation
