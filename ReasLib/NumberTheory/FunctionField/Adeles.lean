/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Adeles and Weil covectors of a one-variable function field

Places of `K / k` are discrete valuation rings of `K` containing `k`. The adele
ring is the restricted product of the completions `K_v` at all such places,
including the place at infinity relative to any affine model. A covector is a
`k`-linear map on the adele ring vanishing on `A(D)` for some divisor `D`.
-/

@[expose] public section

open IsDedekindDomain
open scoped RestrictedProduct RatFunc

noncomputable section

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

namespace FunctionField

/-- A place of a one-variable function field `K / k` is a discrete valuation
subring of `K` containing the constants `k`. -/
structure Place where
  valuationSubring : ValuationSubring K
  containsConstants : ∀ x : k, algebraMap k K x ∈ valuationSubring
  isDiscreteValuationRing : IsDiscreteValuationRing valuationSubring

namespace Place

/-- Construct a place from a discrete valuation subring of `K` containing `k`. -/
def ofValuationSubring (A : ValuationSubring K)
    (containsConstants : ∀ x : k, algebraMap k K x ∈ A)
    (isDiscreteValuationRing : IsDiscreteValuationRing A) : Place k K where
  valuationSubring := A
  containsConstants := containsConstants
  isDiscreteValuationRing := isDiscreteValuationRing

/-- The valuation subring of a constructed place is the chosen subring. -/
theorem ofValuationSubring_valuationSubring (A : ValuationSubring K)
    (containsConstants : ∀ x : k, algebraMap k K x ∈ A)
    (isDiscreteValuationRing : IsDiscreteValuationRing A) :
    (Place.ofValuationSubring k K A containsConstants isDiscreteValuationRing).valuationSubring =
      A := sorry

/-- A constructed place has the chosen valuation subring, contains every constant,
and has a discrete valuation ring as its valuation subring. -/
theorem ofValuationSubring_spec (A : ValuationSubring K)
    (containsConstants : ∀ x : k, algebraMap k K x ∈ A)
    (isDiscreteValuationRing : IsDiscreteValuationRing A) :
    let v := ofValuationSubring k K A containsConstants isDiscreteValuationRing
    v.valuationSubring = A ∧
      (∀ x : k, algebraMap k K x ∈ v.valuationSubring) ∧
      IsDiscreteValuationRing v.valuationSubring := sorry

end Place

/-- The valuation ring of a place is a Dedekind domain. -/
theorem Place.isDedekindDomain (v : Place k K) :
    IsDedekindDomain v.valuationSubring := by
  exact @IsPrincipalIdealRing.isDedekindDomain v.valuationSubring _ inferInstance
    (@IsDiscreteValuationRing.toIsPrincipalIdealRing v.valuationSubring _ inferInstance
      v.isDiscreteValuationRing)

/-- The maximal ideal of the valuation ring at a place, as a height-one prime. -/
abbrev Place.maximalIdeal (v : Place k K) : HeightOneSpectrum v.valuationSubring :=
  @IsDiscreteValuationRing.maximalIdeal v.valuationSubring _ _ v.isDiscreteValuationRing

/-- The completion `K_v` of `K` at a place. -/
abbrev Place.completion (v : Place k K) :=
  @HeightOneSpectrum.adicCompletion v.valuationSubring _ (Place.isDedekindDomain k K v)
    K _ _ _ (Place.maximalIdeal k K v)

/-- `Place.completion` is the adic completion at the maximal ideal. -/
theorem Place.completion_eq (v : Place k K) :
    Place.completion k K v =
      @HeightOneSpectrum.adicCompletion v.valuationSubring _ (Place.isDedekindDomain k K v)
        K _ _ _ (Place.maximalIdeal k K v) :=
  sorry

/-- The integer ring `O_v` in the local completion `K_v`. -/
abbrev Place.completionIntegers (v : Place k K) :=
  @HeightOneSpectrum.adicCompletionIntegers v.valuationSubring _ (Place.isDedekindDomain k K v)
    K _ _ _ (Place.maximalIdeal k K v)

/-- Membership in `O_v` is the valuation inequality `Valued.v x ≤ 1`. -/
theorem Place.mem_completionIntegers_iff (v : Place k K) (x : Place.completion k K v) :
    x ∈ Place.completionIntegers k K v ↔ Valued.v x ≤ 1 :=
  sorry

/-- The local lattice `π_v ^ (-n) O_v` in the completion at a place. -/
def Place.powCompletionIntegers (v : Place k K) (n : ℤ) : Set (Place.completion k K v) :=
  {x : Place.completion k K v | Valued.v x ≤ WithZero.exp n}

/-- Membership in `π_v ^ (-n) O_v` is the corresponding valuation bound. -/
theorem Place.mem_powCompletionIntegers_iff (v : Place k K) (n : ℤ)
    (x : Place.completion k K v) :
    x ∈ Place.powCompletionIntegers k K v n ↔ Valued.v x ≤ WithZero.exp n :=
  sorry

/-- The adele ring of `K / k` is the restricted product of all local completions. -/
abbrev AdeleRing :=
  Πʳ v : Place k K, [Place.completion k K v, Place.completionIntegers k K v]

/-- `AdeleRing k K` is the cofinite restricted product of the local completions. -/
theorem adeleRing_eq :
    AdeleRing k K =
      RestrictedProduct (fun v : Place k K ↦ Place.completion k K v)
        (fun v : Place k K ↦ Place.completionIntegers k K v) Filter.cofinite :=
  sorry

/-- An element of `K` is integral at all but finitely many places. -/
theorem Place.algebraMap_mem_completionIntegers_ae (x : K) :
    ∀ᶠ v in (Filter.cofinite : Filter (Place k K)),
      Algebra.algebraMap K (Place.completion k K v) x ∈ Place.completionIntegers k K v :=
  sorry

namespace AdeleRing

/-- The diagonal embedding of `K` into the adele ring. -/
def diagonal : K →+* AdeleRing k K where
  toFun x :=
    RestrictedProduct.mk
      (fun v : Place k K ↦ Algebra.algebraMap K (Place.completion k K v) x)
      (Place.algebraMap_mem_completionIntegers_ae k K x)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The `v`-component of the diagonal embedding is the local algebra map. -/
theorem diagonal_apply (x : K) (v : Place k K) :
    diagonal k K x v = Algebra.algebraMap K (Place.completion k K v) x :=
  sorry

end AdeleRing

/-- The function field acts on the adele ring through the diagonal embedding. -/
instance instAlgebra_K_adeleRing : Algebra K (AdeleRing k K) :=
  (AdeleRing.diagonal k K).toAlgebra

/-- Constants act on the adele ring through `k → K → A`. -/
instance instAlgebra_k_adeleRing : Algebra k (AdeleRing k K) :=
  ((AdeleRing.diagonal k K).comp (algebraMap k K)).toAlgebra

/-- The actions of `k` and `K` on the adele ring are compatible. -/
instance instIsScalarTower_k_K_adeleRing : IsScalarTower k K (AdeleRing k K) :=
  sorry

/-- A divisor on the places of `K / k` is a finitely supported integer combination. -/
abbrev Divisor := Place k K →₀ ℤ

/-- Evaluating a divisor at a place gives its finitely supported coefficient. -/
theorem divisor_apply (D : Divisor k K) (v : Place k K) : D v = D.toFun v :=
  sorry

/-- The lattice `A(D)` of adeles with the prescribed local valuation bounds. -/
def adeleOf (D : Divisor k K) : Set (AdeleRing k K) :=
  {a : AdeleRing k K |
    ∀ v : Place k K, a v ∈ Place.powCompletionIntegers k K v (D v)}

/-- Membership in `A(D)` is the family of local lattice conditions. -/
theorem mem_adeleOf_iff (D : Divisor k K) (a : AdeleRing k K) :
    a ∈ adeleOf k K D ↔
      ∀ v : Place k K, a v ∈ Place.powCompletionIntegers k K v (D v) :=
  sorry

/-- A covector is a `k`-linear map vanishing on `A(D)` for some divisor `D`. -/
def IsCovector (μ : AdeleRing k K →ₗ[k] k) : Prop :=
  ∃ D : Divisor k K, ∀ a ∈ adeleOf k K D, μ a = 0

/-- A covector is characterized by vanishing on the lattice of a divisor. -/
theorem isCovector_iff (μ : AdeleRing k K →ₗ[k] k) :
    IsCovector k K μ ↔ ∃ D : Divisor k K, ∀ a ∈ adeleOf k K D, μ a = 0 :=
  Iff.rfl

end FunctionField
