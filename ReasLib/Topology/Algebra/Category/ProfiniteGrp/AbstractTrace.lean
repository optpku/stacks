/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.Divisors
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.ContinuousTrace

/-!
# Full abstract continuous trace formula

Numerical data record finite conjugacy-class multiplicities. The trace laws
quantify over finite rings and finite projective left coefficients, and include
perfectness of continuous homology.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open scoped Ring
noncomputable section
universe u v

namespace ProfiniteGrp.ContinuousTrace

variable (S : DegreeExtension.{u})

/-- A positive integer and finite multiplicities of degree-d conjugacy classes. -/
structure AbstractTraceData where
  /-- The distinguished integer. -/
  q : ℕ
  /-- The distinguished integer is positive. -/
  one_le_q : 1 ≤ q
  /-- The finite multiplicities in each positive degree. -/
  multiplicity : ℕ+ → (ConjClasses S.middle →₀ ℕ)
  /-- Nonzero multiplicities are supported on the prescribed degree. -/
  support_degree : ∀ (d : ℕ+) (c : ConjClasses S.middle),
    multiplicity d c ≠ 0 → S.degClass c = hatZNatCast d.val

namespace AbstractTraceData
variable {S}

/-- Construct trace data from finite families of degree-d conjugacy classes. -/
def ofFiniteSets (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses S.middle)
    (hdeg : ∀ d x, S.degClass (F d x) = hatZNatCast d.val) : AbstractTraceData S where
  q := q
  one_le_q := hq
  multiplicity d := ∑ x : ι d, Finsupp.single (F d x) 1
  support_degree := by
    intro d c hc
    by_contra h
    apply hc
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    exact Finsupp.single_eq_of_ne (fun he ↦ h (he.symm ▸ hdeg d x))

/-- The divisor sum in the additive commutator quotient. -/
def leftHandSum {Λ : Type v} [Ring Λ] (T : AbstractTraceData S)
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ) : Λ♮ :=
  ∑ d ∈ n.divisors, if h : 0 < d then
    d • (T.multiplicity ⟨d, h⟩).sum (fun c m ↦ m • conjClassTrace S M (powClass S c (n / d)))
  else 0

/-- The integer weighted count of degree-d classes. -/
def pointCount (T : AbstractTraceData S) (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if h : 0 < d then
    d * (T.multiplicity ⟨d, h⟩).sum (fun _ m ↦ m)
  else 0

/-- The finite-family constructor retains its specified integer. -/
@[simp] theorem ofFiniteSets_q (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses S.middle)
    (hdeg : ∀ d x, S.degClass (F d x) = hatZNatCast d.val) :
    (ofFiniteSets q hq F hdeg).q = q := rfl

/-- Trace data have a positive integer and degree-d support in each multiplicity. -/
theorem spec (T : AbstractTraceData S) :
    1 ≤ T.q ∧ ∀ (d : ℕ+) (c : ConjClasses S.middle),
      T.multiplicity d c ≠ 0 → S.degClass c = hatZNatCast d.val := sorry

/-- Multiply the integer by m and degree-d multiplicities by m^d. -/
def scale (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) : AbstractTraceData S where
  q := m * T.q
  one_le_q := Nat.mul_le_mul hm T.one_le_q
  multiplicity d := m ^ d.val • T.multiplicity d
  support_degree := sorry

/-- Scaling multiplies the distinguished integer by m. -/
theorem scale_q (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) :
    (T.scale m hm).q = m * T.q := sorry

/-- Scaling multiplies degree-d multiplicities by m^d. -/
theorem scale_multiplicity (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) (d : ℕ+) :
    (T.scale m hm).multiplicity d = m ^ d.val • T.multiplicity d := sorry

/-- The scaled divisor sum weights each degree-d summand by m^d. -/
theorem leftHandSum_scale {Λ : Type v} [Ring Λ] (T : AbstractTraceData S)
    (m : ℕ) (hm : 1 ≤ m) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ) :
    (T.scale m hm).leftHandSum M n =
      ∑ d ∈ n.divisors, if h : 0 < d then
        d • (m ^ d • (T.multiplicity ⟨d, h⟩).sum
          (fun c a ↦ a • conjClassTrace S M (powClass S c (n / d))))
      else 0 := sorry

end AbstractTraceData

/-- The continuous trace formula, including well-definedness of every derived trace.
All three fields are propositions. No perfect model or isomorphism is selected here. -/
structure IsAbstractTraceFormula (T : AbstractTraceData S) : Prop where
  /-- Finite continuous cohomological dimension at primes not dividing q. -/
  finite_cd : ∀ ℓ : ℕ, Nat.Prime ℓ → ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G
  /-- Continuous homology of finite projective coefficients is perfect. -/
  homology_perfect : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V],
    DerivedCategory.IsPerfect (derivedCoinvariants S M)
  /-- The divisor sum equals the normalized homological Frobenius trace. -/
  trace_eq : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
    0 < n → T.leftHandSum M n =
      (T.q ^ n) • traceFrobeniusPow S M (homology_perfect hunit M) n

/-- The trace law is unchanged by choosing a different proof of perfectness;
this only varies a proof, never the underlying continuous homology model. -/
theorem IsAbstractTraceFormula.trace_eq_of_perfect {T : AbstractTraceData S}
    (h : IsAbstractTraceFormula S T) {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ) (hn : 0 < n) :
    T.leftHandSum M n = (T.q ^ n) • traceFrobeniusPow S M hperf n :=
  h.trace_eq hunit M n hn

/-- Construct the trace-formula predicate from dimension, perfectness and trace laws. -/
def IsAbstractTraceFormula.ofLaws (T : AbstractTraceData S)
    (hcd : ∀ ℓ : ℕ, Nat.Prime ℓ → ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G)
    (hperf : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
      (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
      [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V],
      DerivedCategory.IsPerfect (derivedCoinvariants S M))
    (htrace : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
      (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
      [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
      0 < n → T.leftHandSum M n =
        (T.q ^ n) • traceFrobeniusPow S M (hperf hunit M) n) :
    IsAbstractTraceFormula S T where
  finite_cd := hcd
  homology_perfect := hperf
  trace_eq := htrace

/-- The trace formula specifies finite prime dimension, perfectness and every trace identity. -/
theorem IsAbstractTraceFormula.spec (T : AbstractTraceData S) :
    IsAbstractTraceFormula S T ↔
      (∀ ℓ : ℕ, Nat.Prime ℓ → ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G) ∧
      (∀ {Λ : Type u} [Ring Λ] [Finite Λ]
        (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
        [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V],
        DerivedCategory.IsPerfect (derivedCoinvariants S M)) ∧
      (∀ {Λ : Type u} [Ring Λ] [Finite Λ]
        (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
        [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
        (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ),
        0 < n → T.leftHandSum M n = (T.q ^ n) • traceFrobeniusPow S M hperf n) := sorry

/-- At a fixed integer, the trace formula determines all conjugacy-class multiplicities. -/
theorem AbstractTraceData.multiplicity_unique {T₁ T₂ : AbstractTraceData S}
    (h₁ : IsAbstractTraceFormula S T₁) (h₂ : IsAbstractTraceFormula S T₂)
    (hq : T₁.q = T₂.q) : T₁.multiplicity = T₂.multiplicity := sorry

/-- Existence of numerical data satisfying the continuous trace formula. -/
def HasAbstractTraceFormula : Prop :=
  ∃ T : AbstractTraceData S, IsAbstractTraceFormula S T

end ProfiniteGrp.ContinuousTrace
