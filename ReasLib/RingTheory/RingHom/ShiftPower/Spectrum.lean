/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable
public import ReasLib.RingTheory.RingHom.ShiftPower.BaseChange
public import ReasLib.RingTheory.RingHom.ShiftPower.Spectrum.Homeomorph
public import ReasLib.RingTheory.RingHom.ShiftPower.PowerSurjective
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral consequences of shift-power generation

This leaf owns the reusable spectral and residue-field consequences of the
shift-power generation predicate. The chapter file can therefore retain only
source-facing packaging and recall blocks.

@stack 09EF
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace ShiftPower

namespace Spectrum

private lemma hom_ext_of_isReduced
    {T : Type*} [CommRing T] [IsReduced T]
    (f : R →+* S) (hgen : IsGenerated f) (g h : S →+* T)
    (hcomp : g.comp f = h.comp f) : g = h := by
  have hle : Subring.closure ((f.range : Set S) ∪ generators f) ≤ g.eqLocus h := by
    apply Subring.closure_le.2
    rintro x (hx | hx)
    · obtain ⟨r, rfl⟩ := hx
      exact DFunLike.congr_fun hcomp r
    · obtain ⟨n, hn, P, hP⟩ := hx
      have heq : (Polynomial.X - Polynomial.C (g x)) ^ n =
          (Polynomial.X - Polynomial.C (h x)) ^ n := by
        calc
          _ = Polynomial.map g (Polynomial.map f P) := by simp [hP]
          _ = Polynomial.map h (Polynomial.map f P) := by
            rw [Polynomial.map_map, Polynomial.map_map, hcomp]
          _ = _ := by simp [hP]
      have hnil : IsNilpotent (h x - g x) := ⟨n, by
        simpa [hn.ne'] using congrArg (Polynomial.eval (h x)) heq⟩
      exact (sub_eq_zero.mp hnil.eq_zero).symm
  apply RingHom.ext
  intro x
  apply hle
  rw [show Subring.closure ((f.range : Set S) ∪ generators f) = ⊤ from hgen]
  trivial

private lemma integral_of_isGenerated (f : R →+* S) (hgen : IsGenerated f) :
    f.IsIntegral := by
  cases subsingleton_or_nontrivial S
  · intro x
    exact ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  · intro x
    apply IsIntegral.of_mem_closure'' ((f.range : Set S) ∪ generators f) ?_ x
    · rw [show Subring.closure ((f.range : Set S) ∪ generators f) = ⊤ from hgen]
      trivial
    · rintro y (hy | hy)
      · obtain ⟨r, rfl⟩ := hy
        exact f.isIntegralElem_map
      · obtain ⟨n, hn, P, hP⟩ := hy
        obtain ⟨Q, hQ, _, hQmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
          (show (Polynomial.X - Polynomial.C y) ^ n ∈ Polynomial.lifts f from ⟨P, hP⟩)
          ((Polynomial.monic_X_sub_C y).pow n)
        exact ⟨Q, hQmonic, by
          rw [Polynomial.eval₂_eq_eval_map, hQ]
          simp [hn.ne']⟩

private lemma generated_tensorProduct
    {R' : Type w} [CommRing R'] [Algebra R S] [Algebra R R']
    (hgen : IsGenerated (algebraMap R S)) :
    IsGenerated (algebraMap R' (R' ⊗[R] S)) := by
  let f := algebraMap R S
  let g := algebraMap R R'
  let T := R' ⊗[R] S
  let j : S →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let B := Subring.closure (((algebraMap R' T).range : Set T) ∪ generators (algebraMap R' T))
  have hleft (r : R') : algebraMap R' T r ∈ B :=
    Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have hcomp : (algebraMap R' T).comp g = j.comp f :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have hcomm (r : R) : algebraMap R' T (g r) = j (f r) := DFunLike.congr_fun hcomp r
  have hright (s : S) : j s ∈ B := by
    have hle : Subring.closure ((f.range : Set S) ∪ generators f) ≤ B.comap j := by
      apply Subring.closure_le.2
      rintro y (hy | hy)
      · obtain ⟨r, rfl⟩ := hy
        change j (f r) ∈ B
        rw [← hcomm]
        exact hleft _
      · obtain ⟨n, hn, P, hP⟩ := hy
        apply Subring.subset_closure
        right
        refine ⟨n, hn, Polynomial.map g P, ?_⟩
        calc
          Polynomial.map (algebraMap R' T) (Polynomial.map g P) =
              Polynomial.map j (Polynomial.map f P) := by
            rw [Polynomial.map_map, Polynomial.map_map, hcomp]
          _ = (Polynomial.X - Polynomial.C (j y)) ^ n := by simp [hP]
    apply hle
    rw [show Subring.closure ((f.range : Set S) ∪ generators f) = ⊤ from hgen]
    trivial
  have hle : Subring.closure
      (Set.range (Algebra.TensorProduct.includeLeft : R' →ₐ[R] T) ∪ Set.range j) ≤ B := by
    apply Subring.closure_le.2
    rintro _ (⟨r, rfl⟩ | ⟨s, rfl⟩)
    · exact hleft r
    · exact hright s
  change Subring.closure
    (Set.range (Algebra.TensorProduct.includeLeft : R' →ₐ[R] T) ∪
      Set.range (Algebra.TensorProduct.includeRight : S →ₐ[R] T)) ≤ B at hle
  rw [Algebra.TensorProduct.closure_range_union_range_eq_top R R' S] at hle
  exact top_le_iff.1 hle

private lemma generated_baseChange
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hgen : IsGenerated f) : IsGenerated (f.baseChange g) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact generated_tensorProduct hgen

private lemma field_mem_range_of_shift_power
    {K A : Type*} [Field K] [CommRing A] [Nontrivial A] (φ : K →+* A)
    {y : A} {n : ℕ} {P : Polynomial K} (hn : (n : K) ≠ 0)
    (hP : Polynomial.map φ P = (Polynomial.X - Polynomial.C y) ^ n) : y ∈ φ.range := by
  have hc := congrArg Polynomial.nextCoeff hP
  rw [Polynomial.nextCoeff_map φ.injective,
    (Polynomial.monic_X_sub_C y).nextCoeff_pow, Polynomial.nextCoeff_X_sub_C] at hc
  have hc' : φ (-P.nextCoeff) = (n : A) * y := by
    simpa [nsmul_eq_mul] using congrArg Neg.neg hc
  refine ⟨(n : K)⁻¹ * -P.nextCoeff, ?_⟩
  rw [map_mul, hc', ← mul_assoc, ← map_natCast φ n, ← map_mul,
    inv_mul_cancel₀ hn, map_one, one_mul]

private lemma field_exists_prime_power
    {K A : Type*} [Field K] [CommRing A] [Nontrivial A] (φ : K →+* A)
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {y : A} {n : ℕ} {P : Polynomial K} (hn : 0 < n)
    (hP : Polynomial.map φ P = (Polynomial.X - Polynomial.C y) ^ n) :
    ∃ k : ℕ, y ^ (p ^ k) ∈ φ.range := by
  have hp : p.Prime := Fact.out
  letI : CharP A p := charP_of_injective_ringHom φ.injective p
  obtain ⟨k, m, hmp, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have he : Polynomial.expand A (p ^ k) ((Polynomial.X - Polynomial.C (y ^ (p ^ k))) ^ m) =
      (Polynomial.X - Polynomial.C y) ^ (p ^ k * m) := by
    simp only [map_pow, map_sub, Polynomial.expand_X, Polynomial.expand_C]
    rw [← sub_pow_char_pow, ← pow_mul]
  have hQ : Polynomial.map φ (Polynomial.contract (p ^ k) P) =
      (Polynomial.X - Polynomial.C (y ^ (p ^ k))) ^ m := by
    rw [Polynomial.map_contract (pow_ne_zero _ hp.ne_zero), hP, hnm, ← he,
      Polynomial.contract_expand (p ^ k) (pow_ne_zero _ hp.ne_zero)]
  exact ⟨k, field_mem_range_of_shift_power φ ((CharP.cast_eq_zero_iff K p m).not.mpr hmp) hQ⟩

/-- A field-source shift-power generated map has a positive source-image power for every target
element. -/
lemma Field.exists_pow_mem
    {K : Type*} {A : Type*} [Field K] [CommRing A] (φ : K →+* A)
    (hgen : IsGenerated φ) :
    ∀ x : A, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ φ.range := by
  cases subsingleton_or_nontrivial A
  · intro x
    exact ⟨1, zero_lt_one, 0, Subsingleton.elim _ _⟩
  · letI := φ.toAlgebra
    obtain hzero | ⟨p, hp, hchar⟩ := CharP.exists' K
    · letI := hzero
      have hle : Subring.closure ((φ.range : Set A) ∪ generators φ) ≤ φ.range := by
        apply Subring.closure_le.2
        rintro y (hy | hy)
        · exact hy
        · obtain ⟨n, hn, P, hP⟩ := hy
          exact field_mem_range_of_shift_power φ (Nat.cast_ne_zero.mpr hn.ne') hP
      intro x
      refine ⟨1, zero_lt_one, ?_⟩
      rw [pow_one]
      apply hle
      rw [show Subring.closure ((φ.range : Set A) ∪ generators φ) = ⊤ from hgen]
      trivial
    · letI := hp
      letI := hchar
      letI : CharP A p := charP_of_injective_ringHom φ.injective p
      have hle : Subring.closure ((φ.range : Set A) ∪ generators φ) ≤
          (Subalgebra.perfectClosure K A p).toSubring := by
        apply Subring.closure_le.2
        rintro y (hy | hy)
        · obtain ⟨r, rfl⟩ := hy
          exact (Subalgebra.perfectClosure K A p).algebraMap_mem r
        · obtain ⟨n, hn, P, hP⟩ := hy
          exact field_exists_prime_power φ hn hP
      intro x
      have hx : x ∈ Subring.closure ((φ.range : Set A) ∪ generators φ) := by
        rw [show Subring.closure ((φ.range : Set A) ∪ generators φ) = ⊤ from hgen]
        trivial
      obtain ⟨k, hk⟩ := hle hx
      exact ⟨p ^ k, pow_pos (show p.Prime from Fact.out).pos _, hk⟩

/-- Shift-power generation makes the map on prime spectra injective. -/
@[stacks 09EF]
theorem comap_injective
    (f : R →+* S) (hgen : IsGenerated f) :
    Function.Injective (comap f) := by
  intro q₁ q₂ heq
  let p := comap f q₁
  let i₁ := Ideal.ResidueField.map p.asIdeal q₁.asIdeal f rfl
  let i₂ := Ideal.ResidueField.map p.asIdeal q₂.asIdeal f
    (congrArg PrimeSpectrum.asIdeal heq)
  letI := i₁.toAlgebra
  letI := i₂.toAlgebra
  let T := q₁.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] q₂.asIdeal.ResidueField
  haveI : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      p.asIdeal.ResidueField _ _ (RingHom.injective _) (RingHom.injective _)
  obtain ⟨t⟩ := (inferInstance : Nonempty (PrimeSpectrum T))
  let j₁ : q₁.asIdeal.ResidueField →+* t.asIdeal.ResidueField :=
    (algebraMap T t.asIdeal.ResidueField).comp Algebra.TensorProduct.includeLeftRingHom
  let j₂ : q₂.asIdeal.ResidueField →+* t.asIdeal.ResidueField :=
    (algebraMap T t.asIdeal.ResidueField).comp Algebra.TensorProduct.includeRight.toRingHom
  have hmaps : j₁.comp (algebraMap S q₁.asIdeal.ResidueField) =
      j₂.comp (algebraMap S q₂.asIdeal.ResidueField) := by
    apply hom_ext_of_isReduced f hgen
    ext r
    change algebraMap T t.asIdeal.ResidueField
        (Algebra.TensorProduct.includeLeftRingHom (algebraMap S q₁.asIdeal.ResidueField (f r))) =
      algebraMap T t.asIdeal.ResidueField
        (Algebra.TensorProduct.includeRight (algebraMap S q₂.asIdeal.ResidueField (f r)))
    rw [← Ideal.ResidueField.map_algebraMap p.asIdeal q₁.asIdeal f rfl,
      ← Ideal.ResidueField.map_algebraMap p.asIdeal q₂.asIdeal f
        (congrArg PrimeSpectrum.asIdeal heq)]
    exact congrArg (algebraMap T t.asIdeal.ResidueField)
      (DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := p.asIdeal.ResidueField)) (algebraMap R p.asIdeal.ResidueField r))
  ext x
  have hxmap : j₁ (algebraMap S q₁.asIdeal.ResidueField x) =
      j₂ (algebraMap S q₂.asIdeal.ResidueField x) := DFunLike.congr_fun hmaps x
  rw [← Ideal.algebraMap_residueField_eq_zero, ← Ideal.algebraMap_residueField_eq_zero]
  constructor
  · intro hx
    apply j₂.injective
    rw [map_zero, ← hxmap, hx, map_zero]
  · intro hx
    apply j₁.injective
    rw [map_zero, hxmap, hx, map_zero]

/-- With locally nilpotent kernel, shift-power generation makes the map on prime spectra
bijective. -/
@[stacks 09EF]
theorem comap_bijective
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    Function.Bijective (comap f) := by
  refine ⟨comap_injective f hgen, ?_⟩
  have hdense := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := f)).2 hker
  have hclosed := (PrimeSpectrum.isClosedMap_comap_of_isIntegral f
    (integral_of_isGenerated f hgen)) _ isClosed_univ
  rw [Set.image_univ] at hclosed
  have hrange : Set.range (comap f) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_range]
  exact Set.range_eq_univ.1 hrange

/-- Shift-power generation implies purely inseparable maps on all residue fields. -/
@[stacks 09EF, stacks 0BRH "purely inseparable residue fields"]
theorem residueField_isPurelyInseparable
    (f : R →+* S) (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable f := by
  intro q
  let p := comap f q
  let i := Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
  letI := i.toAlgebra
  letI : Nonempty (q.asIdeal.ResidueField →+* AlgebraicClosure q.asIdeal.ResidueField) :=
    ⟨algebraMap _ _⟩
  change IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField
  apply IsPurelyInseparable.of_injective_comp_algebraMap
    p.asIdeal.ResidueField q.asIdeal.ResidueField (AlgebraicClosure q.asIdeal.ResidueField)
  intro g h hcomp
  apply Ideal.ResidueField.ringHom_ext
  apply hom_ext_of_isReduced f hgen
  ext r
  have hr := DFunLike.congr_fun hcomp (algebraMap R p.asIdeal.ResidueField r)
  simpa only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, i,
    Ideal.ResidueField.map_algebraMap] using hr

private lemma ker_tensorProduct_isLocallyNilpotent
    {R' : Type w} [CommRing R'] [Algebra R S] [Algebra R R']
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent)
    (hgen : IsGenerated (algebraMap R S)) :
    (RingHom.ker (algebraMap R' (R' ⊗[R] S))).IsLocallyNilpotent := by
  let f := algebraMap R S
  let g := algebraMap R R'
  intro x hx
  rw [mem_nilradical]
  apply nilpotent_iff_mem_prime.2
  intro P hP
  let p' : PrimeSpectrum R' := ⟨P, hP⟩
  let p := comap g p'
  obtain ⟨q, hq⟩ := (comap_bijective f hker hgen).2 p
  let i₁ := Ideal.ResidueField.map p.asIdeal p'.asIdeal g rfl
  let i₂ := Ideal.ResidueField.map p.asIdeal q.asIdeal f
    (congrArg PrimeSpectrum.asIdeal hq).symm
  letI := i₁.toAlgebra
  letI := i₂.toAlgebra
  let T := p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] q.asIdeal.ResidueField
  haveI : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      p.asIdeal.ResidueField _ _ (RingHom.injective _) (RingHom.injective _)
  obtain ⟨t⟩ := (inferInstance : Nonempty (PrimeSpectrum T))
  let j₁ : p'.asIdeal.ResidueField →+* t.asIdeal.ResidueField :=
    (algebraMap T t.asIdeal.ResidueField).comp Algebra.TensorProduct.includeLeftRingHom
  let j₂ : q.asIdeal.ResidueField →+* t.asIdeal.ResidueField :=
    (algebraMap T t.asIdeal.ResidueField).comp Algebra.TensorProduct.includeRight.toRingHom
  let a := j₁.comp (algebraMap R' p'.asIdeal.ResidueField)
  let b := j₂.comp (algebraMap S q.asIdeal.ResidueField)
  have hcomp : a.comp g = b.comp f := by
    ext r
    change algebraMap T t.asIdeal.ResidueField
        (Algebra.TensorProduct.includeLeftRingHom (algebraMap R' p'.asIdeal.ResidueField (g r))) =
      algebraMap T t.asIdeal.ResidueField
        (Algebra.TensorProduct.includeRight (algebraMap S q.asIdeal.ResidueField (f r)))
    rw [← Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal g rfl,
      ← Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal f
        (congrArg PrimeSpectrum.asIdeal hq).symm]
    exact congrArg (algebraMap T t.asIdeal.ResidueField)
      (DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := p.asIdeal.ResidueField)) (algebraMap R p.asIdeal.ResidueField r))
  letI : Algebra R t.asIdeal.ResidueField := (a.comp g).toAlgebra
  haveI : IsScalarTower R R t.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let a' : R' →ₐ[R] t.asIdeal.ResidueField := { a with commutes' _ := rfl }
  let b' : S →ₐ[R] t.asIdeal.ResidueField :=
    { b with commutes' r := (DFunLike.congr_fun hcomp r).symm }
  let L := Algebra.TensorProduct.lift a' b' (fun _ _ ↦ Commute.all ..)
  have hx' : a x = 0 := by
    have hxL := congrArg L (show algebraMap R' (R' ⊗[R] S) x = 0 from hx)
    simpa [L, a', Algebra.TensorProduct.algebraMap_apply] using hxL
  have hxzero : algebraMap R' p'.asIdeal.ResidueField x = 0 := by
    apply j₁.injective
    simpa only [a, RingHom.comp_apply, map_zero] using hx'
  exact Ideal.algebraMap_residueField_eq_zero.1 hxzero

namespace BaseChange

/-- The locally nilpotent kernel condition is preserved under tensor-product base change along an
arbitrary ring homomorphism. -/
@[stacks 09EF]
theorem ker_isLocallyNilpotent
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    (RingHom.ker (f.baseChange g)).IsLocallyNilpotent := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact ker_tensorProduct_isLocallyNilpotent hker hgen

/-- Ambient-algebra specialization of the base-change kernel theorem. -/
theorem ker_isLocallyNilpotent_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    (RingHom.ker (f.baseChangeAlgebraMap (R' := R'))).IsLocallyNilpotent := by
  letI := f.toAlgebra
  exact ker_tensorProduct_isLocallyNilpotent hker hgen

/-- The spectral homeomorphism persists after tensor-product base change along an arbitrary ring
homomorphism. -/
@[stacks 09EF]
theorem isHomeomorph_comap
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    IsHomeomorph (comap (f.baseChange g)) := by
  have hgen' := generated_baseChange f g hgen
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨continuous_comap _, PrimeSpectrum.isClosedMap_comap_of_isIntegral (f.baseChange g)
      (integral_of_isGenerated _ hgen'),
      comap_bijective _ (ker_isLocallyNilpotent f g hker hgen) hgen'⟩

/-- Ambient-algebra specialization of the base-change spectral homeomorphism theorem. -/
theorem isHomeomorph_comap_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hker : (RingHom.ker f).IsLocallyNilpotent)
    (hgen : IsGenerated f) :
    IsHomeomorph (comap (f.baseChangeAlgebraMap (R' := R'))) := by
  letI := f.toAlgebra
  have hgen' := generated_tensorProduct (R' := R') hgen
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨continuous_comap _, PrimeSpectrum.isClosedMap_comap_of_isIntegral _
      (integral_of_isGenerated _ hgen'),
      comap_bijective _ (ker_isLocallyNilpotent_algebraMap f hker hgen) hgen'⟩

/-- Purely inseparable residue-field maps persist after tensor-product base change along an
arbitrary ring homomorphism. -/
@[stacks 09EF]
theorem residueField_isPurelyInseparable
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable (f.baseChange g) :=
  Spectrum.residueField_isPurelyInseparable _ (generated_baseChange f g hgen)

/-- Ambient-algebra specialization of the base-change residue-field theorem. -/
theorem residueField_isPurelyInseparable_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (hgen : IsGenerated f) :
    ResidueField.MapsPurelyInseparable (f.baseChangeAlgebraMap (R' := R')) := by
  letI := f.toAlgebra
  exact Spectrum.residueField_isPurelyInseparable _ (generated_tensorProduct hgen)

end BaseChange

end Spectrum

end ShiftPower

end RingHom
