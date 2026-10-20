/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.KrullDimension.Integral

@[expose] public section

/-!
# Krull Dimension of Polynomial Algebras

This leaf records polynomial-algebra dimension formulae, including the
closed-point local dimension of affine space and the dimension transported by
finite injective polynomial normalizations.
-/

universe u v w

namespace MvPolynomial

variable {k : Type u} [Field k] {ι : Type v} [Finite ι]

/-- Lemma 10.114.1 (2), tag `00OP`: the local ring of affine space over a
field at a closed point has dimension equal to the number of variables. -/
@[stacks 00OP "closed-point local dimension of affine space"]
theorem ringKrullDim_localizationAtMaximal
    (m : MaximalSpectrum (MvPolynomial ι k)) :
    ringKrullDim (Localization.AtPrime m.asIdeal) = (Nat.card ι : WithBot ℕ∞) := sorry

end MvPolynomial

namespace RingHom.IsIntegral

/-- An injective integral map from a polynomial algebra over a field gives the target the Krull
dimension of its finite variable set. -/
theorem ringKrullDim_eq_natCard_of_injective_mvPolynomial
    {k : Type u} [Field k] {ι : Type v} [_root_.Finite ι] {A : Type w} [CommRing A]
    {f : MvPolynomial ι k →+* A} (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A = (Nat.card ι : WithBot ℕ∞) := sorry

end RingHom.IsIntegral

namespace MvPolynomial.AlgHom

/-- A finite injective polynomial-algebra map over a field gives the target the Krull dimension
of its finite variable set. -/
theorem ringKrullDim_eq_natCard_of_injective_finite
    {k : Type u} [Field k] {ι : Type v} [_root_.Finite ι] {A : Type w} [CommRing A] [Algebra k A]
    (g : MvPolynomial ι k →ₐ[k] A)
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim A = (Nat.card ι : WithBot ℕ∞) := sorry

/-- Lemma 10.115.4 (2), tag `00OY`: the `Fin d` specialization of finite injective polynomial
normalization computes the target Krull dimension as `d`. -/
@[stacks 00OY "Krull dimension from a finite injective polynomial normalization"]
theorem ringKrullDim_eq_of_injective_finite
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] A)
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim A = d := sorry

end MvPolynomial.AlgHom
