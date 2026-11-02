/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading.Quotient
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.StrictTransform
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Projective spectra of Rees algebra quotients

The quotient map of Rees algebras induces a continuous map on projective
spectra, identifying the strict transform of a prime vanishing locus.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace ReesAlgebra

variable {A : Type u} [CommRing A]

/-- A prime belongs to the complement of the center precisely when the center
is not contained in that prime. -/
theorem mem_openAway_iff (I : Ideal A) (x : PrimeSpectrum A) :
    x ∈ openAway I ↔ ¬ I ≤ x.asIdeal := Iff.rfl

/-- The homogeneous kernel determines a relevant prime over `p` when the
center is not contained in `p`. -/
def genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ProjectiveSpectrum (Grading.grade I) where
  asHomogeneousIdeal := Grading.strictTransformIdeal I p
  isPrime := Grading.isPrime_toIdeal_strictTransformIdeal I p
  not_irrelevant_le := Grading.not_irrelevant_le_strictTransformIdeal I p hI

/-- The homogeneous ideal of the lift of `p` is the kernel of the Rees quotient. -/
theorem genericLift_asHomogeneousIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (genericLift I p hI).asHomogeneousIdeal = Grading.strictTransformIdeal I p := rfl

/-- The contraction of the lifted prime to the base ring is `p`. -/
theorem genericLift_liesOver (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (toSpec I (genericLift I p hI)).asIdeal = p := by
  ext a
  change algebraMap A (reesAlgebra I) a ∈ Grading.strictTransformIdeal I p ↔ a ∈ p
  rw [Grading.strictTransformIdeal_spec]
  change (∀ n, (Polynomial.C a).coeff n ∈ p) ↔ a ∈ p
  constructor
  · intro h
    simpa using h 0
  · intro ha n
    by_cases hn : n = 0 <;> simp [Polynomial.coeff_C, hn, ha]

private theorem scalar_pow_mul_linear (I : Ideal A) (n : ℕ)
    (a : (I ^ n : Ideal A)) (b : I) :
    algebraMap A (reesAlgebra I) b.1 ^ n * Grading.linear I n a =
      algebraMap A (reesAlgebra I) a.1 * Grading.degreeOne I b ^ n := by
  apply Subtype.ext
  change Polynomial.C b.1 ^ n * Polynomial.monomial n a.1 =
    Polynomial.C a.1 * Polynomial.monomial 1 b.1 ^ n
  simp only [Polynomial.monomial_pow, mul_one, ← Polynomial.C_pow,
    Polynomial.C_mul_monomial, mul_comm]

private theorem degreeOne_notMem_of_notMem_contraction (I : Ideal A)
    (x : ProjectiveSpectrum (Grading.grade I)) (b : I)
    (hb : b.1 ∉ (toSpec I x).asIdeal) :
    Grading.degreeOne I b ∉ x.asHomogeneousIdeal := by
  intro hbT
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn y hy
  change y ∈ Grading.grade I n at hy
  obtain ⟨a, rfl⟩ := hy
  have hprod : algebraMap A (reesAlgebra I) b.1 ^ n * Grading.linear I n a ∈
      x.asHomogeneousIdeal.toIdeal := by
    rw [scalar_pow_mul_linear]
    exact x.asHomogeneousIdeal.toIdeal.mul_mem_left _
      (x.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hbT n hn)
  exact (x.isPrime.mem_or_mem hprod).resolve_left
    (fun h ↦ hb (x.isPrime.mem_of_pow_mem n h))

private theorem linear_mem_iff_of_not_le (I : Ideal A)
    (x : ProjectiveSpectrum (Grading.grade I)) (hI : ¬ I ≤ (toSpec I x).asIdeal)
    (n : ℕ) (a : (I ^ n : Ideal A)) :
    Grading.linear I n a ∈ x.asHomogeneousIdeal ↔ a.1 ∈ (toSpec I x).asIdeal := by
  obtain ⟨b, hbI, hbx⟩ := SetLike.not_le_iff_exists.mp hI
  let b' : I := ⟨b, hbI⟩
  have hbT := degreeOne_notMem_of_notMem_contraction I x b' hbx
  have hbn : algebraMap A (reesAlgebra I) b ^ n ∉ x.asHomogeneousIdeal.toIdeal :=
    fun h ↦ hbx (x.isPrime.mem_of_pow_mem n h)
  have hbTn : Grading.degreeOne I b' ^ n ∉ x.asHomogeneousIdeal.toIdeal :=
    fun h ↦ hbT (x.isPrime.mem_of_pow_mem n h)
  constructor
  · intro ha
    have hm := x.asHomogeneousIdeal.toIdeal.mul_mem_left
      (algebraMap A (reesAlgebra I) b ^ n) ha
    rw [scalar_pow_mul_linear I n a b'] at hm
    exact (x.isPrime.mem_or_mem hm).resolve_right hbTn
  · intro ha
    have hm := x.asHomogeneousIdeal.toIdeal.mul_mem_right (Grading.degreeOne I b' ^ n) ha
    rw [← scalar_pow_mul_linear I n a b'] at hm
    exact (x.isPrime.mem_or_mem hm).resolve_left hbn

private theorem mem_iff_coeff_of_not_le (I : Ideal A)
    (x : ProjectiveSpectrum (Grading.grade I)) (hI : ¬ I ≤ (toSpec I x).asIdeal)
    (f : reesAlgebra I) :
    f ∈ x.asHomogeneousIdeal ↔ ∀ n, f.1.coeff n ∈ (toSpec I x).asIdeal := by
  change f ∈ x.asHomogeneousIdeal.toIdeal ↔ _
  rw [x.asHomogeneousIdeal.isHomogeneous.mem_iff]
  apply forall_congr'
  intro n
  have hd : (DirectSum.decompose (Grading.grade I) f n : reesAlgebra I) =
      Grading.linear I n ⟨f.1.coeff n, f.2 n⟩ := by
    apply Subtype.ext
    exact Grading.decompose_apply I f n
  rw [hd]
  exact linear_mem_iff_of_not_le I x hI n _

/-- A relevant homogeneous prime over `p` equals its canonical lift. -/
theorem genericLift_unique (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p)
    (x : ProjectiveSpectrum (Grading.grade I))
    (hx : (toSpec I x).asIdeal = p) : x = genericLift I p hI := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro f
  rw [genericLift_asHomogeneousIdeal, Grading.strictTransformIdeal_spec,
    mem_iff_coeff_of_not_le I x (by rwa [hx]), hx]

/-- The lifted generic prime belongs to the strict transform of `V(p)`. -/
theorem genericLift_mem_strictTransform (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    genericLift I p hI ∈ strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) := by
  apply subset_closure
  change p ≤ (toSpec I (genericLift I p hI)).asIdeal ∧
    toSpec I (genericLift I p hI) ∈ openAway I
  rw [mem_openAway_iff, genericLift_liesOver]
  exact ⟨le_rfl, hI⟩

/-- The strict transform of `V(p)` is the closure of its lifted generic point
when the center does not contain that generic point. -/
theorem strictTransform_eq_closure_genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      closure {genericLift I p hI} := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ isClosed_closure
    intro x hx
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton, genericLift_asHomogeneousIdeal]
    intro f hf
    apply (mem_iff_coeff_of_not_le I x ((mem_openAway_iff I _).mp hx.2) f).mpr
    intro n
    exact hx.1 ((Grading.strictTransformIdeal_spec I p f).mp hf n)
  · exact closure_minimal (Set.singleton_subset_iff.mpr
      (genericLift_mem_strictTransform I p hI)) (isClosed_strictTransform I _)

/-- The continuous map on projective spectra induced by the graded Rees
quotient map. -/
def quotientComap (I p : Ideal A) :
    ContinuousMap (ProjectiveSpectrum (Grading.grade (I.map (Ideal.Quotient.mk p))))
      (ProjectiveSpectrum (Grading.grade I)) :=
  ProjectiveSpectrum.comap (Grading.quotientGradedMap I p)
    (Grading.quotientGradedMap_map_irrelevant I p)

/-- The induced projective-spectrum map contracts homogeneous prime ideals. -/
theorem quotientComap_apply (I p : Ideal A)
    (x : ProjectiveSpectrum (Grading.grade (I.map (Ideal.Quotient.mk p)))) :
    (quotientComap I p x).asHomogeneousIdeal =
      HomogeneousIdeal.comap (Grading.quotientGradedMap I p) x.asHomogeneousIdeal := rfl

/-- If `q` is not contained in `p`, their sum is not contained in `p`. -/
theorem not_add_le_of_not_le {p q : Ideal A} (h : ¬ q ≤ p) : ¬ p + q ≤ p := by
  rw [Ideal.add_eq_sup]
  exact fun hpq ↦ h (le_trans le_sup_right hpq)

/-- For prime `p`, non-containment of vanishing loci is equivalent to
non-containment of the defining ideals in the reverse direction. -/
theorem not_zeroLocus_subset_iff {p q : Ideal A} [p.IsPrime] :
    ¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A) ↔
      ¬ q ≤ p := by
  apply not_congr
  constructor
  · intro h
    exact h (show (⟨p, inferInstance⟩ : PrimeSpectrum A) ∈
      PrimeSpectrum.zeroLocus (p : Set A) from fun _ ha ↦ ha)
  · exact PrimeSpectrum.zeroLocus_anti_mono_ideal

private theorem strictTransform_eq_zeroLocus_aux (I p : Ideal A) [p.IsPrime] :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      ProjectiveSpectrum.zeroLocus (Grading.grade I) (Grading.strictTransformIdeal I p) := by
  by_cases hI : I ≤ p
  · have hempty : toSpec I ⁻¹' (PrimeSpectrum.zeroLocus (p : Set A) ∩ openAway I) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ((mem_openAway_iff I _).mp hx.2) (hI.trans hx.1)
    rw [strictTransform_def, hempty, closure_empty]
    symm
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply x.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le _).mpr
    intro n hn f hf
    change f ∈ Grading.grade I n at hf
    obtain ⟨a, rfl⟩ := hf
    apply hx
    exact (Grading.strictTransformIdeal_grade I p n a.1 a.2).mpr
      (hI (Ideal.pow_le_self hn.ne' a.2))
  · rw [strictTransform_eq_closure_genericLift I p hI,
      ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton, genericLift_asHomogeneousIdeal]

/-- The projective spectrum of the quotient Rees algebra maps bijectively
onto the strict transform of the prime vanishing locus. -/
theorem quotientComap_bijOn_strictTransform (I p : Ideal A) [p.IsPrime] :
    Set.BijOn (quotientComap I p) Set.univ
      (strictTransform I (PrimeSpectrum.zeroLocus (p : Set A))) := by
  rw [strictTransform_eq_zeroLocus_aux]
  let f := Grading.quotientGradedMap I p
  have hf : Function.Surjective f := Grading.quotientMap_surjective I p
  refine ⟨?_, ?_, ?_⟩
  · intro x _ a ha
    change f a ∈ x.asHomogeneousIdeal
    have ha0 : f a = 0 := ha
    rw [ha0]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem
  · intro x _ y _ hxy
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    exact Ideal.comap_injective_of_surjective f hf
      (congrArg (fun z ↦ z.asHomogeneousIdeal.toIdeal) hxy)
  · intro x hx
    let J := x.asHomogeneousIdeal.map f
    have hker : RingHom.ker f ≤ x.asHomogeneousIdeal.toIdeal := by
      change (Grading.strictTransformIdeal I p).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
      exact hx
    have hcomap : J.comap f = x.asHomogeneousIdeal := by
      apply HomogeneousIdeal.ext
      change (x.asHomogeneousIdeal.toIdeal.map f).comap f = x.asHomogeneousIdeal.toIdeal
      rw [Ideal.comap_map_of_surjective _ hf]
      exact sup_eq_left.mpr hker
    refine ⟨⟨J, Ideal.map_isPrime_of_surjective hf hker, ?_⟩, Set.mem_univ _, ?_⟩
    · intro hJ
      apply x.not_irrelevant_le
      rw [← hcomap]
      apply (HomogeneousIdeal.irrelevant_le _).mpr
      intro n hn a ha
      exact hJ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (f.map_mem ha))
    · apply ProjectiveSpectrum.ext
      exact hcomap

/-- The strict transform of `V(p)` is the projective zero locus of the
homogeneous kernel with degree-`d` piece `I ^ d ∩ p`. -/
theorem strictTransform_eq_zeroLocus (I p : Ideal A) [p.IsPrime] :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      ProjectiveSpectrum.zeroLocus (Grading.grade I) (Grading.strictTransformIdeal I p) :=
  strictTransform_eq_zeroLocus_aux I p

/-- Blowing up `p + q` separates the strict transforms of two incomparable
prime vanishing loci. -/
theorem disjoint_strictTransform (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hpq : ¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A))
    (hqp : ¬ PrimeSpectrum.zeroLocus (q : Set A) ⊆ PrimeSpectrum.zeroLocus (p : Set A)) :
    Disjoint (strictTransform (p + q) (PrimeSpectrum.zeroLocus (p : Set A)))
      (strictTransform (p + q) (PrimeSpectrum.zeroLocus (q : Set A))) := by
  rw [strictTransform_eq_zeroLocus, strictTransform_eq_zeroLocus]
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn f hf
  change f ∈ Grading.grade (p + q) n at hf
  obtain ⟨a, rfl⟩ := hf
  have hsplit : (p + q) ^ n ≤ ((p + q) ^ n ⊓ p) + ((p + q) ^ n ⊓ q) := by
    cases n with
    | zero => exact (Nat.lt_irrefl 0 hn).elim
    | succ n =>
      have hp : p * (p + q) ^ n ≤ (p + q) ^ (n + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mono (by rw [Ideal.add_eq_sup]; exact le_sup_left) le_rfl
      have hq : q * (p + q) ^ n ≤ (p + q) ^ (n + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mono (by rw [Ideal.add_eq_sup]; exact le_sup_right) le_rfl
      calc
        (p + q) ^ (n + 1) = p * (p + q) ^ n + q * (p + q) ^ n := by
          rw [pow_succ', add_mul]
        _ ≤ ((p + q) ^ (n + 1) ⊓ p) + ((p + q) ^ (n + 1) ⊓ q) :=
          add_le_add (le_inf hp Ideal.mul_le_right) (le_inf hq Ideal.mul_le_right)
  have ha := hsplit a.2
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at ha
  obtain ⟨b, hb, c, hc, hbc⟩ := ha
  have hsum : Grading.linear (p + q) n a =
      Grading.linear (p + q) n ⟨b, hb.1⟩ + Grading.linear (p + q) n ⟨c, hc.1⟩ := by
    rw [← map_add]
    exact congrArg (Grading.linear (p + q) n) (Subtype.ext hbc.symm)
  rw [hsum]
  exact x.asHomogeneousIdeal.toIdeal.add_mem
    (hxp ((Grading.strictTransformIdeal_grade (p + q) p n b hb.1).mpr hb.2))
    (hxq ((Grading.strictTransformIdeal_grade (p + q) q n c hc.1).mpr hc.2))

end ReesAlgebra
