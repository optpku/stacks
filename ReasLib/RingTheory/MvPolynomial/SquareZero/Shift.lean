/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import ReasLib.Algebra.Module.CountablyGenerated.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective.Projective
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
public import ReasLib.RingTheory.Ideal.AssociatedPrime.AutoAssociated
public import ReasLib.RingTheory.MvPolynomial.SquareZero
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CrossRefAttribute

/-!
# The square-zero shift counterexample

@stack 05GR

This file owns the explicit countable shift over the square-zero polynomial quotient. Its cokernel
is the standard countably generated flat module that is neither projective nor Mittag-Leffler.
-/

@[expose] public section

open IsLocalRing

universe u

namespace MvPolynomial.SquareZero.Shift

section Data

variable (k : Type u) [CommRing k]

/-- The square-zero coefficient ring in Example 15.15.5. -/
@[stacks 05GR "square-zero coefficient ring"]
abbrev Ring := MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)

/-- The countably generated free module in Example 15.15.5. -/
@[stacks 05GR "countable free module"]
abbrev Free := ℕ →₀ Ring k

/-- The image of the `i`-th polynomial variable in the square-zero quotient. -/
@[stacks 05GR "square-zero variable"]
noncomputable abbrev generator (i : ℕ) : Ring k :=
  MvPolynomial.SquareZero.generator (σ := ℕ) (k := k) i

/-- The family `e_i - x_i e_{i+1}` defining the square-zero shift. -/
@[stacks 05GR "shift family"]
noncomputable def family (i : ℕ) : Free k :=
  Finsupp.single i 1 - Finsupp.single (i + 1) (generator k i)

/-- Example 15.15.5: the linear map `e_i ↦ e_i - x_i e_{i+1}` on the countable free module. -/
@[stacks 05GR "Example 15.15.5, shift map"]
noncomputable def map : Free k →ₗ[Ring k] Free k :=
  Finsupp.linearCombination (Ring k) (family k)

/-- The cokernel of the explicit square-zero shift. -/
@[stacks 05GR "square-zero shift cokernel"]
abbrev Cokernel := Free k ⧸ LinearMap.range (map k)

/-- The square-zero shift on a single basis term. -/
@[stacks 05GR "shift map on basis terms"]
theorem map_single (i : ℕ) (r : Ring k) :
    map k (Finsupp.single i r) =
      Finsupp.single i r - Finsupp.single (i + 1) (generator k i * r) := by
  simp [map, family, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_comm]

private theorem map_apply_zero (l : Free k) : map k l 0 = l 0 := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l m hl hm => simp [hl, hm]
  | single i r => simp [map_single]

private theorem map_apply_succ (l : Free k) (n : ℕ) :
    map k l (n + 1) = l (n + 1) - generator k n * l n := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l m hl hm => simp only [map_add, Finsupp.add_apply, hl, hm, mul_add]; abel
  | single i r =>
    by_cases h : i = n <;> simp_all [map_single, Finsupp.single_apply]

end Data

variable (k : Type u) [Field k]

/-- Example 15.15.5 (1): the square-zero quotient with countably many variables is
auto-associated. -/
@[stacks 05GR "Example 15.15.5 (1), auto-associated square-zero quotient"]
instance ring_isAutoAssociated : IsAutoAssociatedRing (Ring k) := by
  refine { toIsLocalRing := inferInstance, maximalIdeal_weaklyAssociated := ?_ }
  refine ⟨generator k 0, ?_⟩
  rw [← Ideal.radical_minimalPrimes,
    MvPolynomial.SquareZero.generator_torsion_radical_eq_maximalIdeal,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

/-- Example 15.15.5 (2): the square-zero shift is injective. -/
@[stacks 05GR "Example 15.15.5 (2), injective"]
theorem injective : Function.Injective (map k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro l hl
  rw [LinearMap.mem_ker] at hl
  change l = 0
  ext n
  induction n with
  | zero => simpa [map_apply_zero] using congrArg (fun f : Free k => f 0) hl
  | succ n ih =>
    simpa [map_apply_succ, ih] using congrArg (fun f : Free k => f (n + 1)) hl

/-- Example 15.15.5 (3): the square-zero shift is universally injective. -/
@[stacks 05GR "Example 15.15.5 (3), universally injective"]
theorem universallyInjective :
    LinearMap.UniversallyInjective.{u, u, u, u} (map k) := by
  intro Q _ _
  let e := TensorProduct.finsuppScalarLeft (Ring k) Q ℕ
  have hzero (t) : e ((map k).rTensor Q t) 0 = e t 0 := by
    induction t with
    | zero => simp
    | tmul l q => simp [e, map_apply_zero]
    | add t s ht hs => simp [ht, hs]
  have hsucc (t) (n : ℕ) :
      e ((map k).rTensor Q t) (n + 1) =
        e t (n + 1) - generator k n • e t n := by
    induction t with
    | zero => simp
    | tmul l q => simp [e, map_apply_succ, sub_smul, mul_smul]
    | add t s ht hs =>
      simp only [map_add, Finsupp.add_apply, ht, hs, smul_add]
      abel
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro t ht
  have ht0 : (map k).rTensor Q t = 0 := ht
  change t = 0
  apply e.injective
  ext n
  induction n with
  | zero => simpa [ht0] using (hzero t).symm
  | succ n ih => simpa [ht0, ih] using (hsucc t n).symm

/-- Example 15.15.5 (4): reduction of the square-zero shift modulo the maximal ideal is
bijective. Via `MvPolynomial.SquareZero.residueFieldAlgEquiv`, this is the source map
`map k ⊗ id_k`. -/
@[stacks 05GR "Example 15.15.5 (4), residue map bijective"]
theorem quotientMapByMaximalIdeal_bijective :
    Function.Bijective ((map k).quotientMapByIdeal (maximalIdeal (Ring k))) := by
  let p : Submodule (Ring k) (Free k) := maximalIdeal (Ring k) • ⊤
  have hsingle (i : ℕ) (r : Ring k) :
      p.mkQ (Finsupp.single (i + 1) (generator k i * r)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hmem := Submodule.smul_mem_smul
      (MvPolynomial.SquareZero.generator_mem_maximalIdeal (σ := ℕ) (k := k) i)
      (Submodule.mem_top (x := (Finsupp.single (i + 1) r : Free k)))
    simpa [Finsupp.smul_single, smul_eq_mul] using hmem
  have hmap (l : Free k) : p.mkQ (map k l) = p.mkQ l := by
    induction l using Finsupp.induction_linear with
    | zero => simp
    | add l m hl hm => simp only [map_add, hl, hm]
    | single i r => rw [map_single, map_sub, hsingle, sub_zero]
  have hid : (map k).quotientMapByIdeal (maximalIdeal (Ring k)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ l => exact hmap l
  rw [hid]
  exact ⟨Function.injective_id, Function.surjective_id⟩

/-- Example 15.15.5 (5): the square-zero shift is not surjective. -/
@[stacks 05GR "Example 15.15.5 (5), not surjective"]
theorem not_surjective : ¬ Function.Surjective (map k) := by
  intro h
  obtain ⟨l, hl⟩ := h (Finsupp.single 0 1)
  have hcoeff (n : ℕ) : l n = (Finset.range n).prod (generator k) := by
    induction n with
    | zero => simpa [map_apply_zero] using congrArg (fun f : Free k => f 0) hl
    | succ n ih =>
      have hn := congrArg (fun f : Free k => f (n + 1)) hl
      have hrec : l (n + 1) = generator k n * l n :=
        sub_eq_zero.mp (by simpa [map_apply_succ] using hn)
      rw [hrec, ih, Finset.prod_range_succ, mul_comm]
  let n := l.support.sup id + 1
  have hn : n ∉ l.support := by
    intro hn
    exact Nat.not_succ_le_self _ (Finset.le_sup (f := id) hn)
  exact MvPolynomial.SquareZero.prod_generator_ne_zero (σ := ℕ) (k := k)
    (Finset.range n) ((hcoeff n).symm.trans (Finsupp.notMem_support_iff.mp hn))

/-- Example 15.15.5 (6): the injective square-zero shift has no linear retraction. -/
@[stacks 05GR "Example 15.15.5 (6), not split"]
theorem not_split :
    ¬ ∃ r : Free k →ₗ[Ring k] Free k, r.comp (map k) = LinearMap.id := by
  rintro ⟨r, hr⟩
  let v (i : ℕ) := r (Finsupp.single i 1)
  have hrel (i j : ℕ) :
      v i j - generator k i * v (i + 1) j = (Finsupp.single i (1 : Ring k)) j := by
    have h := LinearMap.congr_fun hr (Finsupp.single i 1)
    change r (map k (Finsupp.single i 1)) = Finsupp.single i 1 at h
    rw [map_single, mul_one, map_sub,
      show (Finsupp.single (i + 1) (generator k i) : Free k) =
        generator k i • Finsupp.single (i + 1) 1 by simp [Finsupp.smul_single],
      map_smul] at h
    exact congrArg (fun l : Free k => l j) h
  let n := (v 0).support.sup id + 1
  have hn : n ∉ (v 0).support := by
    intro hn
    exact Nat.not_succ_le_self _ (Finset.le_sup (f := id) hn)
  have hz : v 0 n = 0 := Finsupp.notMem_support_iff.mp hn
  have hprefix (i : ℕ) : i ≤ n → (Finset.range i).prod (generator k) * v i n = 0 := by
    induction i with
    | zero => intro _; simpa using hz
    | succ i ih =>
      intro hi
      have hne : i ≠ n := Nat.ne_of_lt (Nat.lt_of_succ_le hi)
      have hh : v i n = generator k i * v (i + 1) n :=
        sub_eq_zero.mp (by simpa [Finsupp.single_apply, hne] using hrel i n)
      rw [Finset.prod_range_succ, mul_assoc, ← hh]
      exact ih (Nat.le_of_succ_le hi)
  have hsq : generator k n * generator k n = 0 := by
    simpa [pow_two] using MvPolynomial.SquareZero.generator_sq (σ := ℕ) (k := k) n
  have hdiag : generator k n * v n n = generator k n := by
    have h := congrArg (fun a : Ring k => generator k n * a) (hrel n n)
    simpa only [Finsupp.single_eq_same, mul_sub, ← mul_assoc, hsq, zero_mul,
      sub_zero, mul_one] using h
  apply MvPolynomial.SquareZero.prod_generator_ne_zero (σ := ℕ) (k := k) (Finset.range (n + 1))
  calc
    (Finset.range (n + 1)).prod (generator k) =
        (Finset.range n).prod (generator k) * (generator k n * v n n) := by
      rw [hdiag, Finset.prod_range_succ]
    _ = generator k n * ((Finset.range n).prod (generator k) * v n n) := by ac_rfl
    _ = 0 := by rw [hprefix n le_rfl, mul_zero]

/-- Example 15.15.5 (7): the cokernel of the square-zero shift is flat. -/
@[stacks 05GR "Example 15.15.5 (7), flat cokernel"]
theorem cokernel_flat : Module.Flat (Ring k) (Cokernel k) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ g hg
  let q := (LinearMap.range (map k)).mkQ
  let π := (LinearMap.range g).mkQ
  have he : Function.Exact (map k) q :=
    LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  have hgπ : Function.Exact g π :=
    LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx0 : g.lTensor (Cokernel k) x = 0 := hx
  obtain ⟨y, hy⟩ := q.rTensor_surjective A (Submodule.mkQ_surjective _) x
  have hy0 : q.rTensor B (g.lTensor (Free k) y) = 0 := by
    change ((q.rTensor B).comp (g.lTensor (Free k))) y = 0
    rw [LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
    change g.lTensor (Cokernel k) (q.rTensor A y) = 0
    rw [hy, hx0]
  obtain ⟨z, hz⟩ := (rTensor_exact B he (Submodule.mkQ_surjective _) _).mp hy0
  have hz0 : π.lTensor (Free k) z = 0 := by
    apply universallyInjective k (B ⧸ LinearMap.range g) _ _
    calc
      (map k).rTensor (B ⧸ LinearMap.range g) (π.lTensor (Free k) z) =
          π.lTensor (Free k) ((map k).rTensor B z) := by
        change (((map k).rTensor _).comp (π.lTensor (Free k))) z =
          ((π.lTensor (Free k)).comp ((map k).rTensor B)) z
        rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
      _ = π.lTensor (Free k) (g.lTensor (Free k) y) := congrArg _ hz
      _ = 0 := (lTensor_exact (Free k) hgπ (Submodule.mkQ_surjective _)).apply_apply_eq_zero y
      _ = (map k).rTensor (B ⧸ LinearMap.range g) 0 := (map_zero _).symm
  obtain ⟨w, hw⟩ := (lTensor_exact (Free k) hgπ (Submodule.mkQ_surjective _) z).mp hz0
  have hyw : y = (map k).rTensor A w := by
    apply Module.Flat.lTensor_preserves_injective_linearMap g hg
    calc
      g.lTensor (Free k) y = (map k).rTensor B z := hz.symm
      _ = (map k).rTensor B (g.lTensor (Free k) w) := congrArg _ hw.symm
      _ = g.lTensor (Free k) ((map k).rTensor A w) := by
        change (((map k).rTensor B).comp (g.lTensor (Free k))) w =
          ((g.lTensor (Free k)).comp ((map k).rTensor A)) w
        rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  change x = 0
  rw [← hy, hyw]
  exact (rTensor_exact A he (Submodule.mkQ_surjective _)).apply_apply_eq_zero w

/-- Example 15.15.5 (8): the cokernel of the square-zero shift is countably generated. -/
@[stacks 05GR "Example 15.15.5 (8), countably generated cokernel"]
theorem cokernel_countablyGenerated : Module.CountablyGenerated (Ring k) (Cokernel k) := by
  let q := (LinearMap.range (map k)).mkQ
  refine ⟨Set.range (fun i : ℕ => q (Finsupp.single i 1)), Set.countable_range _, ?_⟩
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (map k)) x
  induction l using Finsupp.induction_linear with
  | zero => simpa using (Submodule.zero_mem _)
  | add l m hl hm => simpa only [map_add] using Submodule.add_mem _ hl hm
  | single i r =>
    have h : q (Finsupp.single i r) = r • q (Finsupp.single i 1) := by
      rw [← map_smul]
      simp [Finsupp.smul_single]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Example 15.15.5 (9): the cokernel of the square-zero shift is not projective. -/
@[stacks 05GR "Example 15.15.5 (9), nonprojective cokernel"]
theorem cokernel_not_projective : ¬ Module.Projective (Ring k) (Cokernel k) := by
  intro h
  letI := h
  let q := (LinearMap.range (map k)).mkQ
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let p : Free k →ₗ[Ring k] Free k := LinearMap.id - s.comp q
  have hp (x : Free k) : p x ∈ LinearMap.range (map k) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (x - s (q x)) = 0
    rw [map_sub, show q (s (q x)) = q x from LinearMap.congr_fun hs (q x), sub_self]
  let e := LinearEquiv.ofInjective (map k) (injective k)
  refine not_split k ⟨e.symm.toLinearMap.comp (p.codRestrict _ hp), ?_⟩
  apply LinearMap.ext
  intro x
  apply e.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  apply Subtype.ext
  change p (map k x) = map k x
  have hq : q (map k x) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  simp [p, hq]

/-- Example 15.15.5 (10): the cokernel of the square-zero shift is not Mittag-Leffler. -/
@[stacks 05GR "Example 15.15.5 (10), non-Mittag-Leffler cokernel"]
theorem cokernel_not_mittagLeffler : ¬ Module.MittagLeffler (Ring k) (Cokernel k) := by
  intro h
  exact cokernel_not_projective k
    (Module.Projective.of_flat_mittagLeffler (cokernel_flat k) h (cokernel_countablyGenerated k))

end MvPolynomial.SquareZero.Shift
