module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Hypersurfaces defined by sums of p-th powers

This file provides the coordinate rings and explicit nilpotent witnesses for
hypersurfaces with equation `1 + s X^p + t Y^p`.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial.PthPowerHypersurface

/-- The polynomial `1 + s X₀^p + t X₁^p` over a commutative ring. -/
def relation {K : Type u} [CommRing K] (p : ℕ) (s t : K) :
    MvPolynomial (Fin 2) K :=
  1 + C s * X (0 : Fin 2) ^ p + C t * X (1 : Fin 2) ^ p

/-- The coordinate ring of the hypersurface with equation
`1 + s X₀^p + t X₁^p = 0`. -/
abbrev Ring {K : Type u} [CommRing K] (p : ℕ) (s t : K) :=
  MvPolynomial (Fin 2) K ⧸
    Ideal.span ({relation p s t} : Set (MvPolynomial (Fin 2) K))

/-- The class of `1 + a X₀ + b X₁` in the p-th-power hypersurface ring. -/
def witness {K : Type u} [CommRing K] (p : ℕ) (s t a b : K) : Ring p s t :=
  Ideal.Quotient.mk _ (1 + C a * X (0 : Fin 2) + C b * X (1 : Fin 2))

/-- If `a^p = s` and `b^p = t` in characteristic `p`, the explicit linear
witness has p-th power zero. -/
theorem witness_pow_eq_zero {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (s t a b : K) (ha : a ^ p = s) (hb : b ^ p = t) :
    (witness p s t a b) ^ p = 0 := sorry

/-- When at least one p-th-power coefficient is nonzero, the explicit linear
witness is nonzero in the hypersurface ring. -/
theorem witness_ne_zero {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (s t a b : K) (hst : s ≠ 0 ∨ t ≠ 0) :
    witness p s t a b ≠ 0 := sorry

/-- A p-th-power hypersurface with nonzero coefficient and roots of its two
coefficients is not reduced. -/
theorem not_isReduced {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (s t a b : K) (ha : a ^ p = s) (hb : b ^ p = t)
    (hst : s ≠ 0 ∨ t ≠ 0) :
    ¬ IsReduced (Ring p s t) := sorry

namespace RationalFunctionPlane

/-- The rational function field in two variables over the prime field of
characteristic `p`. -/
abbrev BaseField (p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (MvPolynomial (Fin 2) (ZMod p))

/-- The first coordinate rational function in `BaseField p`. -/
def s (p : ℕ) [Fact p.Prime] : BaseField p :=
  algebraMap (MvPolynomial (Fin 2) (ZMod p)) (BaseField p) (X (0 : Fin 2))

/-- The second coordinate rational function in `BaseField p`. -/
def t (p : ℕ) [Fact p.Prime] : BaseField p :=
  algebraMap (MvPolynomial (Fin 2) (ZMod p)) (BaseField p) (X (1 : Fin 2))

/-- The coordinate ring of the rational-function-plane p-th-power
hypersurface. -/
abbrev baseRing (p : ℕ) [Fact p.Prime] : Type :=
  Ring p (s p) (t p)

/-- The rational-function-plane p-th-power hypersurface has an integral-domain
coordinate ring. -/
instance instIsDomainBaseRing (p : ℕ) [Fact p.Prime] : IsDomain (baseRing p) := sorry

/-- The coordinate ring after extending the two coefficients to a field `L`. -/
abbrev baseChangeRing (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (BaseField p) L] : Type v :=
  Ring p (algebraMap (BaseField p) L (s p))
    (algebraMap (BaseField p) L (t p))

/-- If both coordinate rational functions acquire p-th roots in a field
extension, the extended hypersurface ring is not reduced. -/
theorem baseChangeRing_not_isReduced (p : ℕ) [Fact p.Prime]
    (L : Type v) [Field L] [Algebra (BaseField p) L]
    (ha : ∃ a : L, a ^ p = algebraMap (BaseField p) L (s p))
    (hb : ∃ b : L, b ^ p = algebraMap (BaseField p) L (t p)) :
    ¬ IsReduced (baseChangeRing p L) := sorry

end RationalFunctionPlane

end MvPolynomial.PthPowerHypersurface
