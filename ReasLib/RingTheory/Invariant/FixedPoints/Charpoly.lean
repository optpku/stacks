module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints

@[expose] public section

/-!
# Orbit-polynomial coefficients in fixed-point subrings

This leaf records the coefficient-level descent of the finite orbit polynomial.  The ambient
polynomial and its product presentation remain the canonical Mathlib objects; the bundled
coefficient is the reusable bridge to `FixedPoints.subring` and to ideals of that subring.

@stack 0H34
-/

universe u v

namespace FixedPoints

variable {R : Type u} [CommRing R]

/-- The `n`th coefficient of the finite orbit polynomial, bundled as a fixed element.

The fixedness proof is supplied by `MulSemiringAction.smul_coeff_charpoly`, so the datum is
canonical and does not depend on a chosen representative or on a chapter-local construction. -/
@[stacks 0H34 "orbit-polynomial coefficient in the fixed subring"]
noncomputable def charpolyCoeff (G : Type v) [Group G] [MulSemiringAction G R] [Fintype G]
    (x : R) (n : ℕ) : FixedPoints.subring R G :=
  ⟨(MulSemiringAction.charpoly G x).coeff n,
    fun g ↦ MulSemiringAction.smul_coeff_charpoly x n g⟩

/-- The underlying ring element of `FixedPoints.charpolyCoeff` is the ambient orbit coefficient. -/
@[simp, stacks 0H34 "orbit-polynomial coefficient coercion"]
theorem coe_charpolyCoeff (G : Type v) [Group G] [MulSemiringAction G R] [Fintype G]
    (x : R) (n : ℕ) :
    (charpolyCoeff G x n : R) = (MulSemiringAction.charpoly G x).coeff n := sorry
-- Proof strategy: unfold `charpolyCoeff`; coercion from the fixed-point subtype returns the
-- first component of its defining pair, so the result is definitional.

/-- The fixedness equation carried by an orbit-polynomial coefficient. -/
@[stacks 0H34 "orbit-polynomial coefficient fixedness"]
theorem smul_charpolyCoeff (G : Type v) [Group G] [MulSemiringAction G R] [Fintype G]
    (x : R) (n : ℕ) (g : G) :
    g • (charpolyCoeff G x n : R) = (charpolyCoeff G x n : R) := sorry
-- Proof strategy: use the second component of `charpolyCoeff G x n`, whose fixedness witness is
-- `MulSemiringAction.smul_coeff_charpoly x n`; rewrite coercions with `coe_charpolyCoeff`.

/-- Nonleading orbit-polynomial coefficients lie in the extended fixed-subring ideal.

This is the reusable algebraic core of Stacks tag `0H34`; the source-facing `Fin` indexing is
recovered by applying this theorem with `n = i` and `i.isLt`. -/
@[stacks 0H34 "nonleading orbit coefficients in a fixed-subring ideal"]
theorem charpolyCoeff_mem (G : Type v) [Group G] [MulSemiringAction G R] [Fintype G]
    (J : Ideal (FixedPoints.subring R G)) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    {n : ℕ} (hn : n < Fintype.card G) :
    charpolyCoeff G x n ∈ J := sorry
-- Proof strategy: unfold `Ideal.map` as the ideal span of the image of `J` and use
-- `Submodule.span_induction` to write `x` as a finite sum of terms `f * b`, with `f : J` fixed
-- by `G`.  Strengthen the induction statement to coefficientwise congruence modulo `J` between
-- the orbit polynomials before and after adjoining one such term.  Expand
-- `∏ g : G, (X - C (g • (y - f * b)))` over `Finset.powerset`; every nonconstant correction has
-- a factor `f ^ i`, hence its bundled fixed coefficient lies in `J`, while the constant part is
-- the orbit polynomial of `y`.  The base polynomial at `0` is `X ^ Fintype.card G`; use `hn` and
-- `Polynomial.coeff_X_pow` to remove its leading coefficient, and use
-- `MulSemiringAction.smul_coeff_charpoly` to bundle every coefficient in the fixed subring.

end FixedPoints
