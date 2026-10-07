module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Purely inseparable rational function fields `F_p(t) → F_p(x)`

Over a prime `p` and `n : ℕ`, the pair `Λ = F_p(t_1, …, t_n)` and
`k = F_p(x_1, …, x_n)` with `t_i ↦ x_i^p` is realized as the image of the
fraction-field map induced by `MvPolynomial.expand p`.
-/

@[expose] public section

open MvPolynomial

noncomputable section

namespace PurelyInseparable

/-- Addition in the prime field `F_p` is cancellative. -/
instance instIsCancelAdd_zMod (p : ℕ) [Fact p.Prime] : IsCancelAdd (ZMod p) where
  add_left_cancel a := add_right_injective a
  add_right_cancel a := add_left_injective a

/-- Multivariate polynomials over `F_p` form an integral domain. -/
instance instIsDomain_mvPolynomial (n p : ℕ) [Fact p.Prime] :
    IsDomain (MvPolynomial (Fin n) (ZMod p)) where
  mul_left_cancel_of_ne_zero := sorry
  mul_right_cancel_of_ne_zero := sorry

/-- The rational function field `k = F_p(x_1, …, x_n)`. -/
abbrev functionField (n p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (MvPolynomial (Fin n) (ZMod p))

/-- The rational function field `F_p(x_1, …, x_n)` is a field. -/
instance instField_functionField (n p : ℕ) [Fact p.Prime] : Field (functionField n p) :=
  FractionRing.field _

/-- The fraction-field map induced by `t_i ↦ x_i^p`, i.e. `MvPolynomial.expand p`. -/
def expandFraction (n p : ℕ) [Fact p.Prime] :
    functionField n p →+* functionField n p :=
  let j :=
    (expand p :
        MvPolynomial (Fin n) (ZMod p) →ₐ[ZMod p]
          MvPolynomial (Fin n) (ZMod p)).toRingHom
  IsLocalization.map (functionField n p) j
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j
      (expand_injective (Nat.Prime.pos Fact.out)))

/-- `expandFraction` sends the class of `X i` to the class of `X i ^ p`. -/
theorem expandFraction_X (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    expandFraction n p
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (X i)) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (X i) ^ p :=
  sorry

/-- The image of `expandFraction`, realizing `Λ = F_p(t_1, …, t_n)` inside `functionField`. -/
def lambdaSubfield (n p : ℕ) [Fact p.Prime] : Subfield (functionField n p) :=
  (expandFraction n p).fieldRange

/-- The base field `Λ = F_p(t_1, …, t_n)` as the carrier of `lambdaSubfield`. -/
abbrev lambdaField (n p : ℕ) [Fact p.Prime] : Type :=
  lambdaSubfield n p

/-- The generator `x i` of `k = F_p(x_1, …, x_n)`. -/
def x (n p : ℕ) [Fact p.Prime] (i : Fin n) : functionField n p :=
  algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (X i)

/-- The generator `t i` of `Λ`, the image of `X i` under `expandFraction`. -/
def t (n p : ℕ) [Fact p.Prime] (i : Fin n) : lambdaField n p :=
  (expandFraction n p).rangeRestrictField
    (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (X i))

/-- The generator `x i` is the class of `X i` in the function field. -/
theorem x_eq_algebraMap_X (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    x n p i = algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (X i) :=
  sorry

/-- The structure map `Λ → k` sends `t i` to `x i ^ p`. -/
theorem algebraMap_t (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    algebraMap (lambdaField n p) (functionField n p) (t n p i) = x n p i ^ p :=
  sorry

/-- The extension `k / Λ` is finite; mathematically the degree is `p ^ n`. -/
instance instModuleFinite_functionField (n p : ℕ) [Fact p.Prime] :
    Module.Finite (lambdaField n p) (functionField n p) :=
  sorry

end PurelyInseparable
