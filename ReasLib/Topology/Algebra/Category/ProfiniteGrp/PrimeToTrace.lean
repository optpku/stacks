/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.AbstractTrace
public import ReasLib.NumberTheory.Padics.PrimeTo.SourceArithmetic
public import ReasLib.NumberTheory.Padics.PrimeTo.ArithmeticBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-to procyclic consequences of the continuous trace formula

Trivial coefficients give congruences and exact weighted point-count identities.
The conjugation unit has an explicit integral multiple with bounds controlled by
its first two point counts.
-/

@[expose] public section
open CategoryTheory ProfiniteGrp
open CategoryTheory.Action.ModuleCat
open ProfiniteGrp.ContinuousTrace
noncomputable section
universe u

namespace PadicInt.PrimeTo

variable (extension : DegreeExtension.{u}) (q : ℕ) (hq : 1 ≤ q)
variable {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
variable (F : ∀ d, ι d → ConjClasses extension.middle)
variable (degree_class : ∀ d x, extension.degClass (F d x) = hatZNatCast d.val)
variable (traceFormula : ContinuousTrace.IsAbstractTraceFormula extension
  (ContinuousTrace.AbstractTraceData.ofFiniteSets q hq F degree_class))
variable (kernelEquiv : extension.G ≃ₜ* Multiplicative (PrimeTo q))
variable (unit : (PrimeTo q)ˣ) (frobenius : extension.middle)
variable (degree_frobenius : extension.deg frobenius = hatZOne)
variable (conjugation : ∀ x : extension.G,
  kernelEquiv (extension.conjHom frobenius x) =
    Multiplicative.ofAdd (unit.val * (kernelEquiv x).toAdd))

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- The full continuous trace formula for a prime-to procyclic kernel implies the
trivial-coefficient congruences modulo every positive integer coprime to the distinguished integer. -/
theorem full_formula_trivialModuleCongruence (n : ℕ) (hn : 0 < n)
    (m : ℕ) [NeZero m] (hm : m.Coprime q) :
    trivialModuleCongruence q n m hm unit (natFamily ι) := by
  sorry

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- The product of the distinguished integer and conjugation unit equals that integer
minus the degree-one cardinality. -/
theorem integral_value_of_full_formula :
    (q : PrimeTo q) * unit.val = ((q : ℤ) - Nat.card (ι 1) : ℤ) := by
  exact SourceArithmetic.integral_value_of_first_count q unit (natFamily ι)
    (fun m _ hm ↦ full_formula_trivialModuleCongruence extension q hq F degree_class
      traceFormula kernelEquiv unit frobenius degree_frobenius conjugation 1 (by decide) m hm)

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- The full continuous trace formula implies exact integer weighted divisor-count identities
in every positive degree. -/
theorem integer_count_identity (n : ℕ) (hn : 0 < n) :
    (q : ℤ) ^ n - ((q : ℤ) - Nat.card (ι 1)) ^ n =
      ∑ d ∈ n.divisors, (d * Nat.card (natFamily ι d) : ℤ) := by
  apply int_eq_of_primeTo_reductions q hq
  intro m _ hm
  have hc := full_formula_trivialModuleCongruence extension q hq F degree_class
    traceFormula kernelEquiv unit frobenius degree_frobenius conjugation n hn m hm
  have hv := integral_value_of_full_formula extension q hq F degree_class traceFormula
    kernelEquiv unit frobenius degree_frobenius conjugation
  simp only [trivialModuleCongruence, hv, map_sub, map_pow, map_natCast, map_intCast] at hc
  simpa using hc

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- At degree two the divisor weights are precisely s₁+2s₂. -/
theorem first_two_count_identity :
    (q : ℤ)^2 - ((q : ℤ) - Nat.card (ι 1))^2 =
      (Nat.card (ι 1) : ℤ) + 2 * Nat.card (ι 2) := by
  have h := integer_count_identity extension q hq F degree_class traceFormula
    kernelEquiv unit frobenius degree_frobenius conjugation 2 (by decide)
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  simpa [hdiv, natFamily] using h

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- For a prime-to procyclic kernel satisfying the full continuous trace formula, the product
of the distinguished integer and conjugation unit is an integer in the interval `(-q, q]`.
The absolute-value bound is strict exactly when the degree-one family is nonempty,
and the upper endpoint occurs exactly when every positive-degree family is empty. -/
@[stacks 03VQ]
theorem exists_int_of_full_continuous_trace_formula :
    ∃ a : ℤ, -(q : ℤ) < a ∧ a ≤ q ∧
      (q : PrimeTo q) * unit.val = (a : PrimeTo q) ∧
      (a.natAbs < q ↔ Nonempty (ι 1)) ∧
      (a = q ↔ ∀ d : ℕ+, IsEmpty (ι d)) := by
  let a : ℤ := (q : ℤ) - Nat.card (ι 1)
  have hfirst : (q : ℤ) - a = Nat.card (ι 1) := by dsimp [a]; omega
  have hsecond := first_two_count_identity extension q hq F degree_class traceFormula
    kernelEquiv unit frobenius degree_frobenius conjugation
  have bounds := PrimeToTraceArithmetic.bounds_of_first_two_counts q (Nat.card (ι 1))
    (Nat.card (ι 2)) a hq hfirst hsecond
  refine ⟨a, bounds.1, bounds.2, ?_, ?_, ?_⟩
  · exact integral_value_of_full_formula extension q hq F degree_class traceFormula
      kernelEquiv unit frobenius degree_frobenius conjugation
  · rw [PrimeToTraceArithmetic.strict_iff_degree_one_nonempty q (Nat.card (ι 1))
      (Nat.card (ι 2)) a hq hfirst hsecond]
    exact ⟨fun h ↦ (Nat.card_pos_iff.mp h).1,
      fun h ↦ Nat.card_pos_iff.mpr ⟨h, inferInstance⟩⟩
  · constructor
    · intro ha
      apply all_empty_of_zero_counts
      intro n hn
      have h := integer_count_identity extension q hq F degree_class traceFormula
        kernelEquiv unit frobenius degree_frobenius conjugation n hn
      change (q : ℤ)^n - a^n = _ at h
      rw [ha, sub_self] at h
      exact_mod_cast h.symm
    · intro hempty
      have hzero : Nat.card (ι 1) = 0 := Nat.card_eq_zero.mpr (Or.inl (hempty 1))
      change (q : ℤ) - Nat.card (ι 1) = q
      rw [hzero]
      simp

end PadicInt.PrimeTo
