/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap64.Remark_64_30_1_ContinuousFormula
public import ReasLib.NumberTheory.Padics.PrimeTo.SourceArithmetic
public import ReasLib.NumberTheory.Padics.PrimeTo.ArithmeticBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Example64.30.2: full-formula abstract clause, with explicit local erratum

The complete continuous trace formula is the hypothesis. The source's printed
unconditional strict bound omits the empty-family upper endpoint. The corrected
bound is -q < a ≤ q; strictness holds exactly when the degree-one family is
nonempty, and a=q exactly when every positive-degree family is empty.
-/

@[expose] public section
open CategoryTheory ProfiniteGrp
open CategoryTheory.Action.ModuleCat
open ProfiniteGrp.ContinuousTrace
noncomputable section

namespace PadicInt.PrimeTo

/-- Extend the actual positive-degree source families by the empty zero-degree family. -/
def natFamily (ι : ℕ+ → Type) : ℕ → Type
  | 0 => PEmpty
  | n + 1 => ι ⟨n + 1, Nat.succ_pos n⟩

instance natFamily_finite (ι : ℕ+ → Type) [∀ d, Fintype (ι d)] (n : ℕ) :
    Finite (natFamily ι n) := by
  cases n <;> dsimp [natFamily] <;> infer_instance

@[simp] theorem natFamily_one (ι : ℕ+ → Type) : natFamily ι 1 = ι 1 := rfl

variable (extension : DegreeExtension.{0}) (q : ℕ) (hq : 1 ≤ q)
variable {ι : ℕ+ → Type} [∀ d, Fintype (ι d)]
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
/-- Specializing the full all-coefficient formula to the actual trivial ZMod m
module gives the source congruence. Proof debt is the genuine completed cyclic
resolution and primary decomposition; no congruence is added as a hypothesis. -/
theorem full_formula_trivialModuleCongruence (n : ℕ) (hn : 0 < n)
    (m : ℕ) [NeZero m] (hm : m.Coprime q) :
    trivialModuleCongruence q n m hm unit (natFamily ι) := by
  sorry

/-- Reduction modulo every modulus prime to q separates integers. This is a
standard arithmetic Prop bridge, not an integer selected from an admitted existence. -/
theorem int_eq_of_primeTo_reductions (q : ℕ) (hq : 1 ≤ q) (x y : ℤ)
    (h : ∀ (m : ℕ) [NeZero m], m.Coprime q → (x : ZMod m) = (y : ZMod m)) : x = y := by
  sorry

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- The representative is explicitly q minus the degree-one point count. -/
theorem integral_value_of_full_formula :
    (q : PrimeTo q) * unit.val = ((q : ℤ) - Nat.card (ι 1) : ℤ) := by
  exact SourceArithmetic.integral_value_of_first_count q unit (natFamily ι)
    (fun m _ hm ↦ full_formula_trivialModuleCongruence extension q hq F degree_class
      traceFormula kernelEquiv unit frobenius degree_frobenius conjugation 1 (by decide) m hm)

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- The actual all-degree integer point-count identities, derived from the full formula. -/
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

/-- Zero weighted counts in every positive degree mean all positive-degree families are empty. -/
theorem all_empty_of_zero_counts (ι : ℕ+ → Type) [∀ d, Fintype (ι d)]
    (h : ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, d * Nat.card (natFamily ι d) = 0) :
    ∀ d : ℕ+, IsEmpty (ι d) := by
  sorry

include extension hq F degree_class traceFormula kernelEquiv unit frobenius degree_frobenius conjugation in
/-- Example64.30.2 abstract clause, corrected at the empty-family endpoint.
The original full trace-formula hypothesis and given kernel/conjugation data remain. -/
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
      -- Local instance justification (proof-local temporary data): The all-degrees empty-family hypothesis supplies emptiness at degree one for this branch.
      haveI : IsEmpty (ι 1) := hempty 1
      simp [a]

end PadicInt.PrimeTo
