/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: SelmerGroup.lean:90-92, SelmerGroup.lean:476-479, SelmerGroup.lean:700-888, SelmerGroup.lean:1049-1049.
Changes: extracted dependency layer and narrowed imports; explicit subgroup homomorphism
constructor replaces a version-sensitive `MonoidHom.restrict` call (same Mathlib data);
added a proof of left injectivity using torsion-free integer valuations.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.RingTheory.DedekindDomain.SInteger
public import ReasLib.Algebra.Group.Units.ModPow

/-!
# The Selmer root-class sequence

Mathlib owns `selmerGroup (R := R) (K := K) (S := S) (n := n)`, a subgroup of
`Kˣ/(Kˣ)^n`. This module constructs its maps from S-unit power classes and to
`ClassGroup (S.integer K)`. For nonzero `n`, the latter map has kernel equal to
the S-unit image and range equal to the n-torsion, without any finiteness hypotheses.
It does not identify this arithmetic group with the Selmer group of an abelian variety.
-/

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- The class of an `S`-unit lies in the Selmer group `K(S,n)`. -/
noncomputable def sUnitToSelmer : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    have : v.valuationOfNeZero (x : Kˣ) = 1 :=
      (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by rw [x.property v hv, WithZero.coe_one])
    simp [this]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma coe_sUnitToSelmer (x : S.unit K) :
    (sUnitToSelmer K S n x : Units.modPow K n) = QuotientGroup.mk (x : Kˣ) :=
  rfl

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K(S,n)`. -/
noncomputable def sUnitModPowToSelmer :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (sUnitToSelmer K S n) <| by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

@[simp]
lemma range_sUnitModPowToSelmer :
    (sUnitModPowToSelmer K S n).range = (sUnitToSelmer K S n).range := by
  ext
  exact ⟨by rintro ⟨y, rfl⟩; induction y using QuotientGroup.induction_on with
    | H y => exact ⟨y, rfl⟩, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩

/-- The map from S-unit power classes to Mathlib's arithmetic Selmer group is injective.
If an S-unit is an n-th power in the fraction field, the integer-valued valuations of its
root vanish away from S, since `n ≠ 0`; hence that root is itself an S-unit.
This completes the left end of the sequence without a new carrier or finiteness assumption. -/
theorem sUnitModPowToSelmer_injective [NeZero n] :
    Function.Injective (sUnitModPowToSelmer K S n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro q
  induction q using QuotientGroup.induction_on with
  | H s =>
    intro hs
    rw [MonoidHom.mem_ker] at hs
    have hs0 : (QuotientGroup.mk (s : Kˣ) : Units.modPow K n) = 1 :=
      congrArg Subtype.val hs
    obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp hs0
    have hwS : w ∈ S.unit K := by
      intro v hv
      have hsval : v.valuationOfNeZero (s : Kˣ) = 1 :=
        (v.valuationOfNeZero_eq_iff (s : Kˣ) 1).mpr (by simpa using s.property v hv)
      have hlog := congrArg (fun y : Kˣ ↦ Multiplicative.toAdd (v.valuationOfNeZero y)) hw
      simp only [powMonoidHom_apply, map_pow, toAdd_pow, nsmul_eq_mul, hsval,
        toAdd_one] at hlog
      have hwzero := (mul_eq_zero.mp hlog).resolve_left
        (Int.natCast_ne_zero.mpr (NeZero.ne n))
      have hwval : v.valuationOfNeZero w = 1 :=
        Multiplicative.toAdd.injective (by simpa only [toAdd_one] using hwzero)
      simpa only [WithZero.coe_one] using (v.valuationOfNeZero_eq_iff w 1).mp hwval
    change (QuotientGroup.mk s : S.unit K ⧸
      (powMonoidHom n : S.unit K →* S.unit K).range) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨w, hwS⟩, Subtype.ext hw⟩

/-- Transport of the integer-valued valuation along the spectrum correspondence between the
primes of `R` off `S` and the primes of `𝒪_S`. -/
lemma SInteger.valuationOfNeZero_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (SInteger.heightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj,
    show ((_ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ from
      HeightOneSpectrum.valuationOfNeZero_eq _ u, HeightOneSpectrum.valuationOfNeZero_eq,
    SInteger.valuation_heightOneSpectrumEquiv K S v (u : K)]

/-- The class of `u` lies in the Selmer group `K(S,n)` exactly when
the principal fractional ideal `(u)` of the `S`-integers is `n`-divisible. -/
lemma mem_selmerGroup_iff_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Units.modPow K n) ∈ selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Units.modPow K n) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd
        ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    refine forall_congr' fun w ↦ ?_
    rw [toAdd_valuationOfNeZero, Int.dvd_neg]
    show (n : ℤ) ∣ count K w ((toPrincipalIdeal (S.integer K) K u :
      (FractionalIdeal (S.integer K)⁰ K)ˣ) : FractionalIdeal (S.integer K)⁰ K) ↔ _
    rw [coe_toPrincipalIdeal]
  rw [lhs, rhs]
  constructor
  · intro h w
    rw [show w = SInteger.heightOneSpectrumEquiv K S
        ((SInteger.heightOneSpectrumEquiv K S).symm w) from
        ((SInteger.heightOneSpectrumEquiv K S).apply_symm_apply w).symm,
      SInteger.valuationOfNeZero_heightOneSpectrumEquiv]
    exact h _ ((SInteger.heightOneSpectrumEquiv K S).symm w).property
  · intro h v hv
    have := h (SInteger.heightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [SInteger.valuationOfNeZero_heightOneSpectrumEquiv] at this

/-- The surjection from the `n`-divisible units onto the Selmer group. -/
noncomputable def selmerGroupFromUnits :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  { toFun := fun u ↦ ⟨QuotientGroup.mk (u : Kˣ),
      (mem_selmerGroup_iff_unitsNDivisible K S n (u : Kˣ)).mpr u.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

@[simp] lemma coe_selmerGroupFromUnits (u : unitsNDivisible (S.integer K) K n) :
    (selmerGroupFromUnits K S n u : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) := rfl

lemma selmerGroupFromUnits_surjective :
    Function.Surjective (selmerGroupFromUnits K S n) := by
  intro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u =>
    exact ⟨⟨u, (mem_selmerGroup_iff_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `selmerGroupFromUnits` is contained in that of the `n`-th-root class map:
an `n`-th power has principal `n`-th root. -/
lemma ker_selmerGroupFromUnits_le [NeZero n] :
    (selmerGroupFromUnits K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have : (QuotientGroup.mk (u : Kˣ) : Units.modPow K n) = 1 := congrArg Subtype.val hu
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp this
  exact (nthRootClass_eq_one_iff _ _ (NeZero.ne n) u).mpr ⟨1, w, by
    rw [map_one, one_mul]; exact hw⟩

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the ring of `S`-integers. Obtained by descending `FractionalIdeal.nthRootClass` along
`selmerGroupFromUnits`. -/
noncomputable def toSClassGroup [NeZero n] :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_selmerGroupFromUnits_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm.toMonoidHom

lemma toSClassGroup_selmerGroupFromUnits [NeZero n] (u : unitsNDivisible (S.integer K) K n) :
    toSClassGroup K S n (selmerGroupFromUnits K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm (selmerGroupFromUnits K S n u) =
        QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [toSClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk']

lemma coe_unitEquivUnitsInteger_symm (a : (S.integer K)ˣ) :
    ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
      Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := by
  apply Units.ext
  rw [Set.unitEquivUnitsInteger_symm_apply_coe]
  rfl

/-- Exactness of the fundamental exact sequence in the middle: a Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit. -/
theorem ker_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).ker = (sUnitToSelmer K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
  rw [MonoidHom.mem_ker, toSClassGroup_selmerGroupFromUnits,
    nthRootClass_eq_one_iff _ _ (NeZero.ne n)]
  constructor
  · intro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    show (QuotientGroup.mk _ : Units.modPow K n) = QuotientGroup.mk (u : Kˣ)
    have hwn : (QuotientGroup.mk (w ^ n) : Units.modPow K n) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
    rw [coe_unitEquivUnitsInteger_symm, ← hw, QuotientGroup.mk_mul, hwn]
    exact (mul_one _).symm
  · intro ⟨s, hs⟩
    have hcoe : (QuotientGroup.mk (s : Kˣ) : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) :=
      congrArg Subtype.val hs
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hcoe
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := by
      rw [← coe_unitEquivUnitsInteger_symm, MulEquiv.symm_apply_apply]
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw]
    group

/-- Exactness of the fundamental exact sequence on the right: the image of `toSClassGroup` is
the `n`-torsion of the class group of the `S`-integers. (Surjectivity onto the full class group
fails in general.) -/
theorem range_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).range =
      (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  ext c
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
    rw [toSClassGroup_selmerGroupFromUnits, nthRootClass_apply, ← map_pow, nthRootHom_pow]
    exact ClassGroup.mk_eq_one_iff_exists.mpr ⟨(u : Kˣ), rfl⟩
  · intro hc
    obtain ⟨I, rfl⟩ : ∃ I, ClassGroup.mk K I = c :=
      ClassGroup.induction (K := K) (fun I ↦ ⟨I, rfl⟩) c
    rw [← map_pow, ClassGroup.mk_eq_one_iff_exists] at hc
    obtain ⟨x, hx⟩ := hc
    have hcount (v : HeightOneSpectrum (S.integer K)) :
        count K v ((toPrincipalIdeal (S.integer K) K x : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) =
          n * count K v ((I : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) := by
      rw [hx, Units.val_pow_eq_pow_val, count_pow]
    have hmem : x ∈ unitsNDivisible (S.integer K) K n := fun v ↦ by
      rw [hcount v]; exact Dvd.intro _ rfl
    refine ⟨selmerGroupFromUnits K S n ⟨x, hmem⟩, ?_⟩
    rw [toSClassGroup_selmerGroupFromUnits, nthRootClass_apply]
    congr 1
    refine count_injective fun v ↦ ?_
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcount v,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne n))]

end IsDedekindDomain

end
