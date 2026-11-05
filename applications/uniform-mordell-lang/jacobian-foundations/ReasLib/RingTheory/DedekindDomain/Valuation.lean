/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: Basic.lean:426-473, Basic.lean:486-512, Basic.lean:713-713.
Changes: extracted and narrowed imports; finite support proved from ideal factorization;
added two general Selmer membership criteria preserving Mathlib valuation normalization.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import ReasLib.RingTheory.DedekindDomain.FractionalIdeal

/-!
# Valuation API for S-integers and Selmer groups

The carrier of every valuation and Selmer group is owned by Mathlib. In its multiplicative
normalization a prime has valuation `exp (-1)`; the additive value on a principal ideal is
the negative of its ideal multiplicity. Divisibility by any natural exponent is preserved
under this sign. These computation lemmas are used by S-integer spectrum transport and
the Selmer exact sequence.
-/

@[expose] public section

section DedekindDomain

open IsDedekindDomain
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  have hf : (Function.support fun v : HeightOneSpectrum R ↦
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)).Finite := by
    have := FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton R⁰ x)
    simpa [Function.support, Filter.eventually_cofinite] using this
  refine hf.subset fun v hv ↦ ?_
  change FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x) ≠ 0
  intro h0
  apply hv
  rw [FractionalIdeal.valuation_eq_exp_neg_count v hx, h0, neg_zero]
  rfl

lemma Set.integer_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    S.integer K ≤ T.integer K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

/-- Ideal-level divisibility characterization of `Associates.count`: the multiplicity of `v` in
`J` is at least `k` iff `v ^ k` divides `J`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- Divisibility characterization of `Associates.count` for a height one prime: the `v`-adic
valuation of `x` is at least `k` iff `x ∈ v ^ k`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- The image of the class of a unit `u` under the `v`-adic valuation mod `n` is the class in
`ZMod n` of the `v`-adic order of `u`. This is the computation rule that
`Mathlib.RingTheory.DedekindDomain.SelmerGroup` lacks; it holds by definition, but the
`Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod` blocks unfolding it by hand. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk (v : HeightOneSpectrum R)
    (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ZMod n) :=
  rfl

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod_mk, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If a power of the prime `v` is generated by `π`, then `π` is a `w`-adic unit at every prime
`w ≠ v`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
    {v w : HeightOneSpectrum R} (hne : w ≠ v) {n : ℕ} {π : R}
    (h : v.asIdeal ^ n = Ideal.span {π}) :
    w.valuation K (algebraMap R K π) = 1 := by
  refine w.valuation_eq_one_iff_notMem.mpr fun hmem ↦ hne (HeightOneSpectrum.ext ?_).symm
  refine v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le (n := n) ?_)
  rwa [h, Ideal.span_le, Set.singleton_subset_iff]

/-- A representative belongs to Mathlib's Selmer group exactly when its integer-valued
valuations outside `S` are divisible by `n`. No positivity hypothesis is needed. -/
lemma IsDedekindDomain.mem_selmerGroup_mk_iff_valuation
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (u : Kˣ) :
    (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
      selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd
        ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
  forall₂_congr fun v _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v n u

/-- Ideal multiplicities give the same Selmer condition. Mathlib's multiplicative
valuation has additive value `-count`; integer divisibility removes this sign. -/
lemma IsDedekindDomain.mem_selmerGroup_mk_iff_count
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (u : Kˣ) :
    (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
      selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
  rw [mem_selmerGroup_mk_iff_valuation]
  exact forall₂_congr fun v _ ↦ by
    rw [FractionalIdeal.toAdd_valuationOfNeZero, Int.dvd_neg]

end DedekindDomain

end
