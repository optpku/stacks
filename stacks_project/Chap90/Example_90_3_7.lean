module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Definition_90_19_2_DualNumber

/-!
# An inseparable fibre product that is not an object of `C_Λ`

Over `Λ = F_p(t_1,…,t_n) → k = F_p(x_1,…,x_n)`, `t_i ↦ x_i^p`, the dual-number object
`k[ε]` lies in `ArtinianLocalAlgCat`. A `Λ`-derivation `D` of `k` yields a morphism
`f_D` with `a ↦ inl a + inr (D a)`. For `D = ∂/∂x_1` and the inclusion `a ↦ a`, the
algebra fibre product is `{a ∈ k | ∂/∂x_1(a) = 0}` and does not surject onto `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

noncomputable section

/-- Addition in the prime field `F_p` is cancellative. -/
instance instIsCancelAdd_zMod (p : ℕ) [Fact p.Prime] : IsCancelAdd (ZMod p) where
  add_left_cancel a := add_right_injective a
  add_right_cancel a := add_left_injective a

/-- Multivariate polynomials over `F_p` form an integral domain. -/
instance instIsDomain_mvPolynomial (n p : ℕ) [Fact p.Prime] :
    IsDomain (MvPolynomial (Fin n) (ZMod p)) where
  mul_left_cancel_of_ne_zero := sorry
  mul_right_cancel_of_ne_zero := sorry

/-- The rational function field `k = F_p(x_1,…,x_n)`. -/
abbrev functionField (n p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (MvPolynomial (Fin n) (ZMod p))

/-- The rational function field `F_p(x_1,…,x_n)` is a field. -/
instance instField_functionField (n p : ℕ) [Fact p.Prime] : Field (functionField n p) :=
  FractionRing.field _

/-- The fraction-field map induced by `t_i ↦ x_i^p`, i.e. `MvPolynomial.expand p`. -/
def expandFraction (n p : ℕ) [Fact p.Prime] :
    functionField n p →+* functionField n p :=
  let j :=
    (MvPolynomial.expand p :
        MvPolynomial (Fin n) (ZMod p) →ₐ[ZMod p]
          MvPolynomial (Fin n) (ZMod p)).toRingHom
  IsLocalization.map (functionField n p) j
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j
      (MvPolynomial.expand_injective (Nat.Prime.pos Fact.out)))

/-- `expandFraction` sends the class of `X i` to the class of `X i ^ p`. -/
theorem expandFraction_X (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    expandFraction n p
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.X i)) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.X i) ^ p :=
  sorry

/-- The image of `expandFraction`, realizing `Λ = F_p(t_1,…,t_n)` inside `functionField`. -/
def lambdaSubfield (n p : ℕ) [Fact p.Prime] : Subfield (functionField n p) :=
  (expandFraction n p).fieldRange

/-- The base field `Λ = F_p(t_1,…,t_n)` as the carrier of `lambdaSubfield`. -/
abbrev LambdaField (n p : ℕ) [Fact p.Prime] : Type := lambdaSubfield n p

/-- The structure map `Λ → k` sends the image of `t_i` to `x_i^p`. -/
theorem algebraMap_lambda_X (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    algebraMap (LambdaField n p) (functionField n p)
        ((expandFraction n p).rangeRestrictField
          (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.X i))) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.X i) ^ p :=
  sorry

/-- The extension `k / Λ` is finite; mathematically the degree is `p^n`. -/
instance instModuleFinite_functionField (n p : ℕ) [Fact p.Prime] :
    Module.Finite (LambdaField n p) (functionField n p) := sorry

/-- The partial derivative `∂/∂x_i` on `functionField`, as a derivation over `LambdaField`. -/
def pderivFunctionField (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    Derivation (LambdaField n p) (functionField n p) (functionField n p) where
  toFun z :=
    let x := (IsFractionRing.div_surjective (MvPolynomial (Fin n) (ZMod p)) z).choose
    let y :=
      (IsFractionRing.div_surjective (MvPolynomial (Fin n) (ZMod p)) z).choose_spec.choose
    (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.pderiv i x) *
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) y -
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) x *
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.pderiv i y)) /
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) y ^ 2
  map_add' := sorry
  map_smul' := sorry
  map_one_eq_zero' := sorry
  leibniz' := sorry

/-- `pderivFunctionField` extends `MvPolynomial.pderiv` along `algebraMap` into the
function field. -/
theorem pderivFunctionField_algebraMap (n p : ℕ) [Fact p.Prime] (i : Fin n)
    (f : MvPolynomial (Fin n) (ZMod p)) :
    pderivFunctionField n p i
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) f) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.pderiv i f) := sorry

/-- `∂/∂x_i` of the generator `x_i` is `1`. -/
theorem pderivFunctionField_X (n p : ℕ) [Fact p.Prime] (i : Fin n) :
    pderivFunctionField n p i
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X i)) = 1 := sorry

/-- `∂/∂x_i` vanishes on the generators `x_j` for `j ≠ i`. -/
theorem pderivFunctionField_X_of_ne (n p : ℕ) [Fact p.Prime] {i j : Fin n} (h : j ≠ i) :
    pderivFunctionField n p i
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X j)) = 0 := sorry

namespace ArtinianLocalAlgCat

variable {Λ k : Type} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The morphism `f_D : k ⟶ k[ε]` of `ArtinianLocalAlgCat` sending `a` to
`inl a + inr (D a)`. -/
def homOfDerivation (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun a ↦ inl a + inr (D a)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `homOfDerivation D` evaluates to the dual number with scalar `a` and infinitesimal `D a`. -/
theorem homOfDerivation_apply (D : Derivation Λ k k) (a : k) :
    (homOfDerivation D).hom a = inl a + inr (D a) := sorry

/-- The algebra fibre product of `f_D` and the inclusion `a ↦ a` consists of the pairs
`(a, a)` with `D a = 0`. -/
theorem mem_algebraPullback_iff (D : Derivation Λ k k) {a b : k} :
    (a, b) ∈ AlgHom.pullback (homOfDerivation D).hom (residueToDualNumber Λ k).hom ↔
      a = b ∧ D a = 0 := sorry

/-- Example 90.3.7: the algebra fibre product of `f_{∂/∂x_1}` and the inclusion
`a ↦ a` into dual numbers does not surject onto the residue field `functionField`,
so that fibre product is not an object of `ArtinianLocalAlgCat`. -/
@[stacks 06S4]
theorem not_surjective_algebraPullback_toResidue (n p : ℕ) [Fact p.Prime] [NeZero n] :
    ¬ Function.Surjective
        (AlgHom.pullbackFst
          (homOfDerivation (pderivFunctionField n p 0)).hom
          (residueToDualNumber (LambdaField n p) (functionField n p)).hom) := sorry

end ArtinianLocalAlgCat

