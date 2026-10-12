/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.Algebra.Category.ModuleCat.Biproducts
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Biproduct
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Colimit
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum
import ReasLib.RingTheory.Flatness.ZMod

@[expose] public section

/-!
# Example 10.82.6

@stack 058N

The three examples are represented by explicit short complexes.  The first is the canonical
direct-sum-to-product quotient sequence over `ℤ`; the second is the split self-sum sequence of a
non-flat module; the third is their biproduct.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped DirectSum

local notation "directSumToProduct" =>
  (DirectSum.coeFnLinearMap ℤ : (⨁ _ : ℕ, ℤ) →ₗ[ℤ] (ℕ → ℤ))

/-- The quotient map from the integer product by the image of the integer direct sum. -/
def integerProductModuloDirectSum :
    (ℕ → ℤ) →ₗ[ℤ] ((ℕ → ℤ) ⧸ LinearMap.range directSumToProduct) :=
  (LinearMap.range directSumToProduct).mkQ

/-- The canonical short complex `⨁ n, ℤ ⟶ (ℕ → ℤ) ⟶ (ℕ → ℤ) ⧸ (⨁ n, ℤ)`. -/
def integerDirectSumProductShortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero
    directSumToProduct integerProductModuloDirectSum
    (LinearMap.range_mkQ_comp directSumToProduct)

/-- The integer sequence `(2, 2^2, 2^3, ...)`. -/
def integerDivisibilityWitness : ℕ → ℤ :=
  fun n ↦ (2 : ℤ) ^ (n + 1)

/-- The class of `(2, 2^2, 2^3, ...)` in the product modulo the direct sum. -/
def integerDivisibilityWitnessClass : integerDirectSumProductShortComplex.X₃ :=
  integerProductModuloDirectSum integerDivisibilityWitness

private theorem integerFunction_mem_range_directSumToProduct_of_finiteSupport
    (f : ℕ → ℤ) (s : Finset ℕ) (hf : ∀ i, i ∉ s → f i = 0) :
    f ∈ LinearMap.range directSumToProduct := by
  classical
  let x : ⨁ _ : ℕ, ℤ := DFinsupp.mk s fun i ↦ f i
  refine ⟨x, ?_⟩
  ext i
  change x i = f i
  by_cases hi : i ∈ s
  · simp [x, hi]
  · simp [x, hi, hf i hi]

private theorem integerFunction_mem_range_directSumToProduct_of_smul_mem
    {r : ℤ} (hr : r ≠ 0) {f : ℕ → ℤ}
    (hf : r • f ∈ LinearMap.range directSumToProduct) :
    f ∈ LinearMap.range directSumToProduct := by
  rcases hf with ⟨x, hx⟩
  apply integerFunction_mem_range_directSumToProduct_of_finiteSupport f x.support
  intro i hi
  have hxi : x i = 0 := (DFinsupp.notMem_support_iff).1 hi
  have hri : r * f i = 0 := by
    have hi' := congrFun hx i
    change x i = r * f i at hi'
    exact hi'.symm.trans hxi
  exact (mul_eq_zero.mp hri).resolve_left hr

private theorem integerDirectSumProductShortComplex_shortExact :
    integerDirectSumProductShortComplex.ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact directSumToProduct integerProductModuloDirectSum
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _
  · change Function.Injective directSumToProduct
    exact DFunLike.coe_injective
  · change Function.Surjective integerProductModuloDirectSum
    exact Submodule.mkQ_surjective _

/-- The product-modulo-direct-sum quotient is torsion-free over `ℤ`. -/
theorem integerProductQuotient_isTorsionFree :
    Module.IsTorsionFree ℤ integerDirectSumProductShortComplex.X₃ := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r q hq
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
      apply (Submodule.Quotient.mk_eq_zero _).2
      apply integerFunction_mem_range_directSumToProduct_of_smul_mem hr
      apply (Submodule.Quotient.mk_eq_zero _).1
      rw [Submodule.Quotient.mk_smul]
      exact hq

/-- The distinguished quotient class is nonzero. -/
theorem integerDivisibilityWitnessClass_ne_zero :
    integerDivisibilityWitnessClass ≠ 0 := by
  intro hzero
  have hmem : integerDivisibilityWitness ∈ LinearMap.range directSumToProduct :=
    (Submodule.Quotient.mk_eq_zero _).1 hzero
  rcases hmem with ⟨x, hx⟩
  obtain ⟨i, hi⟩ : ∃ i, i ∉ x.support := by
    by_cases hne : x.support.Nonempty
    · refine ⟨x.support.max' hne + 1, ?_⟩
      intro hi
      exact Nat.not_succ_le_self _ (x.support.le_max' _ hi)
    · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩
  have hxi : x i = 0 := (DFinsupp.notMem_support_iff).1 hi
  have hi' := congrFun hx i
  change x i = (2 : ℤ) ^ (i + 1) at hi'
  exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0) (hi'.symm.trans hxi)

private def integerDivisibilityRoot (n : ℕ) : ℕ → ℤ :=
  fun i ↦ if n ≤ i + 1 then (2 : ℤ) ^ (i + 1 - n) else 0

/-- The distinguished quotient class is divisible by every power of `2`. -/
theorem integerDivisibilityWitnessClass_two_pow_divisible (n : ℕ) :
    ∃ y : integerDirectSumProductShortComplex.X₃,
      ((2 : ℤ) ^ n) • y = integerDivisibilityWitnessClass := by
  refine ⟨integerProductModuloDirectSum (integerDivisibilityRoot n), ?_⟩
  change (LinearMap.range directSumToProduct).mkQ
      (((2 : ℤ) ^ n) • integerDivisibilityRoot n) =
    (LinearMap.range directSumToProduct).mkQ integerDivisibilityWitness
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  apply integerFunction_mem_range_directSumToProduct_of_finiteSupport
    (((2 : ℤ) ^ n) • integerDivisibilityRoot n - integerDivisibilityWitness)
    (Finset.range n)
  intro i hi
  have hni : n ≤ i := Nat.le_of_not_gt (by simpa using hi)
  have hni' : n ≤ i + 1 := hni.trans (Nat.le_succ i)
  change (2 : ℤ) ^ n * integerDivisibilityRoot n i - (2 : ℤ) ^ (i + 1) = 0
  rw [integerDivisibilityRoot, if_pos hni', sub_eq_zero, ← pow_add,
    Nat.add_sub_of_le hni']

/-- Every map from the quotient to the product kills the distinguished class. -/
theorem integer_direct_sum_product_hom_kills_witness
    (φ : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ)) :
    φ integerDivisibilityWitnessClass = 0 := by
  ext i
  by_contra hi
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (Int.natAbs (φ integerDivisibilityWitnessClass i))
      (by norm_num : (1 : ℕ) < 2)
  obtain ⟨y, hy⟩ := integerDivisibilityWitnessClass_two_pow_divisible n
  have hdvd : (2 : ℤ) ^ n ∣ φ integerDivisibilityWitnessClass i := by
    refine ⟨φ y i, ?_⟩
    have heq := congrArg (fun z : ℕ → ℤ ↦ z i) (congrArg φ hy)
    simpa [Pi.smul_apply, smul_eq_mul] using heq.symm
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hi
  have : (2 : ℕ) ^ n ≤ Int.natAbs (φ integerDivisibilityWitnessClass i) := by
    simpa using hle
  exact (not_lt_of_ge this) hn

/-- The quotient map in the integer sequence has no linear section. -/
theorem integer_direct_sum_product_quotientMap_has_no_section :
    ¬ ∃ s : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ),
      integerProductModuloDirectSum.comp s = LinearMap.id := by
  rintro ⟨s, hs⟩
  apply integerDivisibilityWitnessClass_ne_zero
  calc
    integerDivisibilityWitnessClass = LinearMap.id integerDivisibilityWitnessClass := rfl
    _ = integerProductModuloDirectSum (s integerDivisibilityWitnessClass) := by
      exact (LinearMap.congr_fun hs integerDivisibilityWitnessClass).symm
    _ = integerProductModuloDirectSum 0 := by
      rw [integer_direct_sum_product_hom_kills_witness s]
    _ = 0 := map_zero _

/-- Example 10.82.6 (1): the integer direct-sum/product quotient sequence is universally exact. -/
@[stacks 058N]
theorem integer_direct_sum_product_sequence_universally_exact :
    integerDirectSumProductShortComplex.UniversallyExact := by
  letI : Module.IsTorsionFree ℤ integerDirectSumProductShortComplex.X₃ :=
    integerProductQuotient_isTorsionFree
  letI : Module.Flat ℤ integerDirectSumProductShortComplex.X₃ := inferInstance
  exact integerDirectSumProductShortComplex_shortExact.universallyExact_of_flat_X₃

/-- Example 10.82.6 (2): the left term of the integer sequence is flat. -/
@[stacks 058N]
theorem integerDirectSum_flat :
    Module.Flat ℤ integerDirectSumProductShortComplex.X₁ := by
  exact Module.Flat.dfinsupp

/-- Example 10.82.6 (3): the middle term of the integer sequence is flat. -/
@[stacks 058N]
theorem integerProduct_flat :
    Module.Flat ℤ integerDirectSumProductShortComplex.X₂ := by
  letI : Module.IsTorsionFree ℤ (ℕ → ℤ) := inferInstance
  change Module.Flat ℤ (ℕ → ℤ)
  infer_instance

/-- Example 10.82.6 (4): the right term of the integer sequence is flat. -/
@[stacks 058N]
theorem integerProductQuotient_flat :
    Module.Flat ℤ integerDirectSumProductShortComplex.X₃ := by
  letI : Module.IsTorsionFree ℤ integerDirectSumProductShortComplex.X₃ :=
    integerProductQuotient_isTorsionFree
  exact inferInstance

/-- Example 10.82.6 (5): the integer direct-sum/product quotient sequence does not split. -/
@[stacks 058N]
theorem integer_direct_sum_product_sequence_not_split :
    ¬ Nonempty integerDirectSumProductShortComplex.Splitting := by
  rintro ⟨s⟩
  apply integer_direct_sum_product_quotientMap_has_no_section
  refine ⟨s.s.hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom s.s_g

/-- The composite in the canonical self-sum sequence is zero. -/
lemma selfSumShortComplex_comp_eq_zero {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (biprod.inl : M ⟶ M ⊞ M) ≫ (biprod.snd : M ⊞ M ⟶ M) = 0 := by
  simp

/-- The split short complex `M ⟶ M ⊞ M ⟶ M`. -/
def selfSumShortComplex {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk biprod.inl biprod.snd (selfSumShortComplex_comp_eq_zero M)

/-- Example 10.82.6 (6): the split self-sum sequence is universally exact. -/
@[stacks 058N]
theorem selfSumShortComplex_universallyExact
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (selfSumShortComplex M).UniversallyExact := by
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct M M).universallyExact

private theorem moduleFlat_right_of_biprod
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)
    (h : Module.Flat R ((M ⊞ N : ModuleCat.{u} R) : Type u)) : Module.Flat R N := by
  letI : Module.Flat R ((M ⊞ N : ModuleCat.{u} R) : Type u) := h
  apply Module.Flat.of_retract
    ((biprod.inr : N ⟶ M ⊞ N).hom) ((biprod.snd : M ⊞ N ⟶ N).hom)
  change ((biprod.snd : M ⊞ N ⟶ N).hom).comp
      ((biprod.inr : N ⟶ M ⊞ N).hom) = LinearMap.id
  exact congrArg ModuleCat.Hom.hom
    (biprod.inr_snd : (biprod.inr : N ⟶ M ⊞ N) ≫ biprod.snd = 𝟙 N)

private theorem moduleFlat_right_of_biprod_of_iso
    {R : Type u} [CommRing R] (P M N : ModuleCat.{u} R)
    (h : Module.Flat R P) (e : P ≅ M ⊞ N) : Module.Flat R N := by
  letI : Module.Flat R P := h
  have hMN : Module.Flat R ((M ⊞ N : ModuleCat.{u} R) : Type u) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  exact moduleFlat_right_of_biprod M N hMN

/-- Example 10.82.6 (7): if `M` is non-flat, the left term of its self-sum sequence is non-flat. -/
@[stacks 058N]
theorem selfSumShortComplex_not_flat_X₁
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₁ := by
  intro h
  apply hM
  letI : Module.Flat R (selfSumShortComplex M).X₁ := h
  have e : M ≅ (selfSumShortComplex M).X₁ := Iso.refl M
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Example 10.82.6 (8): if `M` is non-flat, the middle term of its self-sum sequence is
non-flat. -/
@[stacks 058N]
theorem selfSumShortComplex_not_flat_X₂
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₂ := by
  intro h
  apply hM
  exact moduleFlat_right_of_biprod M M h

/-- Example 10.82.6 (9): if `M` is non-flat, the right term of its self-sum sequence is non-flat. -/
@[stacks 058N]
theorem selfSumShortComplex_not_flat_X₃
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₃ := by
  intro h
  apply hM
  letI : Module.Flat R (selfSumShortComplex M).X₃ := h
  have e : M ≅ (selfSumShortComplex M).X₃ := Iso.refl M
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The biproduct of the non-split integer sequence and the self-sum sequence for `ZMod 2`. -/
def universallyExactNonsplitNonflatShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  integerDirectSumProductShortComplex ⊞ selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))

/-- Example 10.82.6 (10): the combined short complex is universally exact. -/
@[stacks 058N]
theorem universallyExactNonsplitNonflatShortComplex_universallyExact :
    universallyExactNonsplitNonflatShortComplex.UniversallyExact :=
  integer_direct_sum_product_sequence_universally_exact.biprod
    (selfSumShortComplex_universallyExact (ModuleCat.of ℤ (ZMod 2)))

/-- Example 10.82.6 (11): the combined short complex does not split. -/
@[stacks 058N]
theorem universallyExactNonsplitNonflatShortComplex_not_split :
    ¬ Nonempty universallyExactNonsplitNonflatShortComplex.Splitting := by
  let T := selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))
  change ¬ Nonempty (integerDirectSumProductShortComplex ⊞ T).Splitting
  rintro ⟨σ⟩
  apply integer_direct_sum_product_quotientMap_has_no_section
  let ι : integerDirectSumProductShortComplex ⟶
      integerDirectSumProductShortComplex ⊞ T := biprod.inl
  let π : integerDirectSumProductShortComplex ⊞ T ⟶
      integerDirectSumProductShortComplex := biprod.fst
  let s : integerDirectSumProductShortComplex.X₃ ⟶
      integerDirectSumProductShortComplex.X₂ := ι.τ₃ ≫ σ.s ≫ π.τ₂
  refine ⟨s.hom, ?_⟩
  have hs : s ≫ integerDirectSumProductShortComplex.g = 𝟙 _ := by
    dsimp [s]
    rw [Category.assoc, Category.assoc, π.comm₂₃]
    rw [σ.s_g_assoc]
    exact congrArg (fun f : integerDirectSumProductShortComplex ⟶
      integerDirectSumProductShortComplex ↦ f.τ₃)
        (biprod.inl_fst : ι ≫ π = 𝟙 integerDirectSumProductShortComplex)
  exact congrArg ModuleCat.Hom.hom hs

/-- Example 10.82.6 (12): the left term of the combined short complex is non-flat. -/
@[stacks 058N]
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₁ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₁ := by
  intro h
  apply selfSumShortComplex_not_flat_X₁
    (ModuleCat.of ℤ (ZMod 2)) (ZMod.not_flat 2 (by decide))
  exact moduleFlat_right_of_biprod_of_iso _ _ _ h
    (ShortComplex.biprodX₁Iso integerDirectSumProductShortComplex
      (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))))

/-- Example 10.82.6 (13): the middle term of the combined short complex is non-flat. -/
@[stacks 058N]
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₂ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₂ := by
  intro h
  apply selfSumShortComplex_not_flat_X₂
    (ModuleCat.of ℤ (ZMod 2)) (ZMod.not_flat 2 (by decide))
  exact moduleFlat_right_of_biprod_of_iso _ _ _ h
    (ShortComplex.biprodX₂Iso integerDirectSumProductShortComplex
      (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))))

/-- Example 10.82.6 (14): the right term of the combined short complex is non-flat. -/
@[stacks 058N]
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₃ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₃ := by
  intro h
  apply selfSumShortComplex_not_flat_X₃
    (ModuleCat.of ℤ (ZMod 2)) (ZMod.not_flat 2 (by decide))
  exact moduleFlat_right_of_biprod_of_iso _ _ _ h
    (ShortComplex.biprodX₃Iso integerDirectSumProductShortComplex
      (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))))

/-- Example 10.82.6: there is a universally exact non-split short complex of integer modules
whose three terms are all non-flat. -/
@[stacks 058N]
theorem exists_universally_exact_nonsplit_nonflat_sequence :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ),
      S.UniversallyExact ∧ ¬ Nonempty S.Splitting ∧
        ¬ Module.Flat ℤ S.X₁ ∧ ¬ Module.Flat ℤ S.X₂ ∧ ¬ Module.Flat ℤ S.X₃ := by
  exact ⟨universallyExactNonsplitNonflatShortComplex,
    universallyExactNonsplitNonflatShortComplex_universallyExact,
    universallyExactNonsplitNonflatShortComplex_not_split,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₁,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₂,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₃⟩

#check @CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃
#check @CategoryTheory.ShortComplex.Splitting.universallyExact
#check @CategoryTheory.ShortComplex.UniversallyExact.biprod

#print axioms integerProductModuloDirectSum
#print axioms integerDirectSumProductShortComplex
#print axioms integerDivisibilityWitness
#print axioms integerDivisibilityWitnessClass
#print axioms selfSumShortComplex
#print axioms universallyExactNonsplitNonflatShortComplex
#print axioms integer_direct_sum_product_sequence_universally_exact
#print axioms integer_direct_sum_product_sequence_not_split
#print axioms selfSumShortComplex_universallyExact
#print axioms universallyExactNonsplitNonflatShortComplex_universallyExact
#print axioms universallyExactNonsplitNonflatShortComplex_not_split
#print axioms universallyExactNonsplitNonflatShortComplex_not_flat_X₁
#print axioms universallyExactNonsplitNonflatShortComplex_not_flat_X₂
#print axioms universallyExactNonsplitNonflatShortComplex_not_flat_X₃
#print axioms exists_universally_exact_nonsplit_nonflat_sequence
