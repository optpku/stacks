/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: Basic.lean:309-320, SelmerGroup.lean:476-694, SelmerGroup.lean:1049-1049.
Changes: extracted arithmetic dependency layers, narrowed imports, and documented ownership.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.RingTheory.DedekindDomain.Valuation
public import ReasLib.RingTheory.DedekindDomain.FractionalIdeal
public import ReasLib.GroupTheory.Finiteness.Abelian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Tactic.Choose

/-!
# Finite generation and rank of Mathlib S-units

The datum is Mathlib's subgroup `S.unit K ≤ Kˣ`. Its valuation map to `ℤ^S` has
kernel canonically isomorphic to `Rˣ`. Finite generation needs only `Group.FG Rˣ` and
finite `S`; the rank formula additionally uses finite `ClassGroup R`. These distinct
hypotheses are kept on their respective statements. Consumers include S-integer unit
calculations, descent, and power-class bounds.
-/

@[expose] public section

open FractionalIdeal

private lemma sUnit_linearIndependent_of_diagonal {ι A : Type*} [CommRing A] [NoZeroDivisors A]
    {u : ι → ι → A} (hd : ∀ i, u i i ≠ 0) (ho : ∀ i j, j ≠ i → u i j = 0) :
    LinearIndependent A u := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg i
  rw [Finset.sum_apply, Pi.zero_apply,
    Finset.sum_eq_single i
      (fun j _ hji ↦ by rw [Pi.smul_apply, ho j i (fun hc ↦ hji (hc ▸ rfl)), smul_zero])
      (fun hni ↦ absurd hi hni),
    Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (hd i)

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-!
### `S`-units

`Set.unit S K` is the subgroup of `x : Kˣ` with `v x = 1` for all `v ∉ S`. Sending `x` to its
tuple of valuations at the primes *in* `S` gives a homomorphism to `ℤ^S` whose kernel is the
group of `∅`-units, i.e. `Rˣ`. When `S` is finite this exhibits `Set.unit S K` as an extension
of a subgroup of a free abelian group of finite rank by `Rˣ`.
-/

variable (S : Set (HeightOneSpectrum R))

/-- The tuple of `v`-adic valuations of an `S`-unit at the primes `v ∈ S`. -/
noncomputable def sUnitValuation : S.unit K →* (S → Multiplicative ℤ) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ)
  map_one' := funext fun _ ↦ map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl

@[simp]
lemma sUnitValuation_apply (x : S.unit K) (v : S) :
    sUnitValuation K S x v = (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ) :=
  rfl

/-- The kernel of `sUnitValuation` consists of the `∅`-units, i.e. of the units of `R`. -/
theorem ker_sUnitValuation :
    (sUnitValuation K S).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext x
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, sUnitValuation_apply,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx v _ ↦ ?_, fun hx v ↦ ?_⟩
  · by_cases hv : v ∈ S
    · simpa using (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mp (hx ⟨v, hv⟩)
    · exact x.property v hv
  · exact (v.1.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by
      simpa using hx v.1 (Set.notMem_empty _))

variable (R) in
/-- The `∅`-units of `K` are the units of `R`. -/
noncomputable def unitsEquivEmptyUnit : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).unit K :=
  let e₁ : R ≃ₐ[R] (⊥ : Subalgebra R K) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).symm
  let e₂ : (⊥ : Subalgebra R K) ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
    Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K).symm
  (Units.mapEquiv (e₁.trans e₂).toRingEquiv.toMulEquiv).trans (Set.unitEquivUnitsInteger _ K).symm

@[simp]
lemma coe_unitsEquivEmptyUnit (a : Rˣ) :
    ((unitsEquivEmptyUnit R K a : ↥((∅ : Set (HeightOneSpectrum R)).unit K)) : Kˣ) =
      Units.map (algebraMap R K : R →* K) a :=
  Units.ext rfl

/-- **Dirichlet's `S`-unit theorem**, weak form: if `Rˣ` is finitely generated and `S` is finite,
then the group of `S`-units is finitely generated.

The map `sUnitValuation` has finitely generated image (a subgroup of the free abelian group
`ℤ^S` of finite rank) and kernel isomorphic to `Rˣ` (`ker_sUnitValuation`,
`unitsEquivEmptyUnit`), and an extension of a finitely generated group by a finitely generated
group is finitely generated. -/
theorem fg_sUnit [Group.FG Rˣ] (hS : S.Finite) : Group.FG (S.unit K) := by
  have : Finite S := hS.to_subtype
  refine Group.fg_of_fg_ker_of_fg_range (sUnitValuation K S) ?_ (Subgroup.fg_of_commGroup_fg _)
  rw [ker_sUnitValuation]
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K) :=
    Group.fg_of_surjective (f := (unitsEquivEmptyUnit R K).toMonoidHom)
      (unitsEquivEmptyUnit R K).surjective
  have hle : (∅ : Set (HeightOneSpectrum R)).unit K ≤ S.unit K := Set.unit_mono S.empty_subset
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective

/-!
### The rank of the `S`-unit group

Strengthening `fg_sUnit`: if moreover the class group of `R` is finite, then the rank of the
`S`-unit group is exactly `rank Rˣ + |S|` (**Dirichlet's `S`-unit theorem**, rank version).
The point is that the valuation map `sUnitValuation` then has full-rank image: for each
`v ∈ S`, some power `v ^ n` is principal (`HeightOneSpectrum.exists_pow_eq_span`), and its
generator is an `S`-unit whose valuation vector is a nonzero multiple of the `v`-th standard
basis vector.
-/

section Rank

open Module

/-- The logarithmic valuation map on `S`-units, with values in `ℤ ^ S`: the additive form of
`sUnitValuation`. This is the `S`-unit analogue of `NumberField.Units.logEmbedding`. -/
noncomputable def sUnitLog : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x w ↦ Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w)
      map_zero' := by ext w; simp
      map_add' := fun x y ↦ by ext w; simp }

@[simp]
lemma sUnitLog_apply (x : Additive (S.unit K)) (w : S) :
    sUnitLog K S x w = Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) :=
  rfl

/-- The kernel of `sUnitLog` is the kernel of `sUnitValuation`, i.e. the `∅`-units. -/
lemma mem_ker_sUnitLog_iff (x : Additive (S.unit K)) :
    x ∈ LinearMap.ker (sUnitLog K S) ↔
      Additive.toMul x ∈ MonoidHom.ker (sUnitValuation K S) := by
  simp only [LinearMap.mem_ker, MonoidHom.mem_ker]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · ext w
    have h2 : Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) = 0 :=
      congrFun hx w
    simpa using toAdd_eq_zero.mp h2
  · ext w
    show Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) = 0
    rw [hx]
    rfl

/-- The kernel of `sUnitLog` is (additively) the unit group of `R`. -/
noncomputable def sUnitLogKerEquiv : ↥(LinearMap.ker (sUnitLog K S)) ≃ₗ[ℤ] Additive Rˣ :=
  have ekermul : ↥(MonoidHom.ker (sUnitValuation K S)) ≃* Rˣ :=
    ((unitsEquivEmptyUnit R K).trans <|
      ((Subgroup.subgroupOfEquivOfLe (Set.unit_mono S.empty_subset)).symm.trans
        (MulEquiv.subgroupCongr (ker_sUnitValuation K S)).symm)).symm
  AddEquiv.toIntLinearEquiv <|
    AddEquiv.trans
      { toFun := fun x ↦ Additive.ofMul (⟨Additive.toMul x.1, (mem_ker_sUnitLog_iff K S _).mp x.2⟩ :
          ↥(MonoidHom.ker (sUnitValuation K S)))
        invFun := fun y ↦ ⟨Additive.ofMul ((Additive.toMul y : _) : S.unit K),
          (mem_ker_sUnitLog_iff K S _).mpr (Additive.toMul y).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
      (MulEquiv.toAdditive ekermul)

variable [Finite (ClassGroup R)]

/-- Each prime `v ∈ S` supports an `S`-unit whose valuation vector is a nonzero multiple of the
standard basis vector at `v` (a generator of a principal power of `v`). -/
lemma exists_sUnit_valuation_single (v : S) :
    ∃ (x : S.unit K) (n : ℤ), n ≠ 0 ∧ sUnitValuation K S x v = Multiplicative.ofAdd n ∧
      ∀ w : S, w ≠ v → sUnitValuation K S x w = 1 := by
  classical
  obtain ⟨h, π, hpos, hπ0, hπ⟩ := (v : HeightOneSpectrum R).exists_pow_eq_span
  have hπK : algebraMap R K π ≠ 0 :=
    fun h0 ↦ hπ0 (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  -- `π` is a unit at every prime other than `v`, in particular an `S`-unit
  have hmem : Units.mk0 (algebraMap R K π) hπK ∈ S.unit K := fun w hw ↦
    HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
      (fun hc ↦ hw (by rw [hc]; exact v.2)) hπ
  -- its valuation vector is `-h` at `v` and `0` elsewhere
  have hval (w : S) : Multiplicative.toAdd
      (sUnitValuation K S ⟨Units.mk0 (algebraMap R K π) hπK, hmem⟩ w) =
        -(if (w : HeightOneSpectrum R) = v then (h : ℤ) else 0) := by
    show Multiplicative.toAdd
      ((w : HeightOneSpectrum R).valuationOfNeZero (Units.mk0 (algebraMap R K π) hπK)) = _
    rw [toAdd_valuationOfNeZero, Units.val_mk0, ← coeIdeal_span_singleton, ← hπ, coeIdeal_pow,
      count_pow, count_maximal]
    simp only [mul_ite, mul_one, mul_zero]
    exact congrArg Neg.neg (if_congr eq_comm rfl rfl)
  refine ⟨⟨Units.mk0 (algebraMap R K π) hπK, hmem⟩, -(h : ℤ),
    neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hpos.ne'), ?_, fun w hne ↦ ?_⟩
  · exact Multiplicative.toAdd.injective (by rw [toAdd_ofAdd, hval v, if_pos rfl])
  · exact Multiplicative.toAdd.injective (by
      rw [toAdd_one, hval w, if_neg (fun hc ↦ hne (Subtype.ext hc)), neg_zero])

open Module in
/-- The range of `sUnitLog` has full rank `|S|`: it contains the diagonal family of `S`-units
provided by `exists_sUnit_valuation_single`. -/
lemma finrank_range_sUnitLog (hS : S.Finite) :
    finrank ℤ ↥(LinearMap.range (sUnitLog K S)) = S.ncard := by
  classical
  have hSfin : Finite S := hS.to_subtype
  have hSfin' : Fintype S := Fintype.ofFinite S
  choose x n hn hxv hxw using fun v : S ↦ exists_sUnit_valuation_single K S v
  have hψx (v w : S) : sUnitLog K S (Additive.ofMul (x v)) w = if w = v then n v else 0 := by
    rw [sUnitLog_apply]
    rcases eq_or_ne w v with rfl | hne
    · rw [if_pos rfl, toMul_ofMul, hxv w, toAdd_ofAdd]
    · rw [if_neg hne, toMul_ofMul, hxw v w hne, toAdd_one]
  have hfam : LinearIndependent ℤ fun v : S ↦ sUnitLog K S (Additive.ofMul (x v)) := by
    refine sUnit_linearIndependent_of_diagonal (fun v ↦ ?_) (fun v w hne ↦ ?_)
    · rw [hψx v v, if_pos rfl]
      exact hn v
    · rw [hψx v w, if_neg hne]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  refine le_antisymm ?_ ?_
  · have h := Submodule.finrank_le (LinearMap.range (sUnitLog K S))
    rwa [finrank_fintype_fun_eq_card] at h
  · have hfam' : LinearIndependent ℤ fun v : S ↦
        (⟨sUnitLog K S (Additive.ofMul (x v)), LinearMap.mem_range_self _ _⟩ :
          ↥(LinearMap.range (sUnitLog K S))) :=
      hfam.of_comp (LinearMap.range (sUnitLog K S)).subtype
    exact hfam'.fintype_card_le_finrank

open Module in
/-- **Dirichlet's `S`-unit theorem**, rank version: if the class group of `R` is finite, `Rˣ` is
finitely generated and `S` is finite, then the `S`-unit group has rank `rank Rˣ + |S|`. -/
theorem finrank_sUnit [Group.FG Rˣ] (hS : S.Finite) :
    finrank ℤ (Additive (S.unit K)) = finrank ℤ (Additive Rˣ) + S.ncard := by
  have hFG : Group.FG (S.unit K) := fg_sUnit K S hS
  have hMfin : Module.Finite ℤ (Additive (S.unit K)) := Module.finite_int_additive _
  -- rank additivity along `sUnitLog`
  have hadd := Submodule.rank_quotient_add_rank (LinearMap.ker (sUnitLog K S))
  have hM := rank_lt_aleph0 ℤ (Additive (S.unit K))
  rw [← hadd] at hM
  have htn := congrArg Cardinal.toNat hadd
  rw [Cardinal.toNat_add (le_self_add.trans_lt hM) (le_add_self.trans_lt hM)] at htn
  -- the quotient is the range, the kernel is `Rˣ`
  have h₁ := congrArg Cardinal.toNat (LinearMap.quotKerEquivRange (sUnitLog K S)).lift_rank_eq
  have h₂ := congrArg Cardinal.toNat (sUnitLogKerEquiv K S).lift_rank_eq
  simp only [Cardinal.toNat_lift] at h₁ h₂
  rw [h₁, h₂] at htn
  rw [show Cardinal.toNat (Module.rank ℤ ↥(LinearMap.range (sUnitLog K S))) =
      finrank ℤ ↥(LinearMap.range (sUnitLog K S)) from rfl, finrank_range_sUnitLog K S hS] at htn
  have htn' : S.ncard + finrank ℤ (Additive Rˣ) = finrank ℤ (Additive (S.unit K)) := htn
  rw [← htn', Nat.add_comm]

end Rank

end IsDedekindDomain

end
