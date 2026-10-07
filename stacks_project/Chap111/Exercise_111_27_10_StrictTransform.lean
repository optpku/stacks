module

public import stacks_project.Chap111.Exercise_111_27_10_Kernel
public import stacks_project.Chap111.Exercise_111_27_8_StrictTransform
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Strict transform of a prime vanishing locus in Proj of a Rees algebra

This file records the unique lift `ξ'` of the generic point of `PrimeSpectrum.zeroLocus p`
and the continuous map `ProjectiveSpectrum (grade (I.map (Ideal.Quotient.mk p))) →
ProjectiveSpectrum (grade I)` induced by the Rees quotient map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace ReesAlgebra

variable {A : Type u} [CommRing A]

/-- A point of `Spec A` lies in `openAway I` if and only if `I` is not contained in its
underlying prime. -/
theorem mem_openAway_iff (I : Ideal A) (x : PrimeSpectrum A) :
    x ∈ openAway I ↔ ¬ I ≤ x.asIdeal := sorry

/-- The unique point `ξ'` of `ProjectiveSpectrum (Grading.grade I)` lying over the generic
point of `PrimeSpectrum.zeroLocus p`. -/
def genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ProjectiveSpectrum (Grading.grade I) where
  asHomogeneousIdeal := Grading.strictTransformIdeal I p
  isPrime := Grading.isPrime_toIdeal_strictTransformIdeal I p
  not_irrelevant_le := Grading.not_irrelevant_le_strictTransformIdeal I p hI

/-- The homogeneous prime of `genericLift I p hI` is `Grading.strictTransformIdeal I p`. -/
theorem genericLift_asHomogeneousIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (genericLift I p hI).asHomogeneousIdeal = Grading.strictTransformIdeal I p := sorry

/-- `genericLift I p hI` lies over the prime `p`. -/
theorem genericLift_liesOver (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (toSpec I (genericLift I p hI)).asIdeal = p := sorry

/-- Any point of `ProjectiveSpectrum (Grading.grade I)` lying over `p` equals
`genericLift I p hI`. -/
theorem genericLift_unique (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p)
    (x : ProjectiveSpectrum (Grading.grade I))
    (hx : (toSpec I x).asIdeal = p) : x = genericLift I p hI := sorry

/-- `genericLift I p hI` belongs to the topological strict transform of
`PrimeSpectrum.zeroLocus p`. -/
theorem genericLift_mem_strictTransform (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    genericLift I p hI ∈ strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) := sorry

/-- The topological strict transform of `PrimeSpectrum.zeroLocus p` is the closure of the
singleton `{genericLift I p hI}`. -/
theorem strictTransform_eq_closure_genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      closure {genericLift I p hI} := sorry

/-- The continuous map on projective spectra induced by `Grading.quotientGradedMap I p`. -/
def quotientComap (I p : Ideal A) :
    ContinuousMap (ProjectiveSpectrum (Grading.grade (I.map (Ideal.Quotient.mk p))))
      (ProjectiveSpectrum (Grading.grade I)) :=
  ProjectiveSpectrum.comap (Grading.quotientGradedMap I p)
    (Grading.quotientGradedMap_map_irrelevant I p)

/-- `quotientComap I p` pulls homogeneous primes back along `Grading.quotientGradedMap I p`. -/
theorem quotientComap_apply (I p : Ideal A)
    (x : ProjectiveSpectrum (Grading.grade (I.map (Ideal.Quotient.mk p)))) :
    (quotientComap I p x).asHomogeneousIdeal =
      HomogeneousIdeal.comap (Grading.quotientGradedMap I p) x.asHomogeneousIdeal := sorry

/-- If `q` is not contained in `p`, then `p + q` is not contained in `p`. -/
theorem not_add_le_of_not_le {p q : Ideal A} (h : ¬ q ≤ p) : ¬ p + q ≤ p := sorry

/-- For a prime `p`, non-containment of vanishing loci is equivalent to non-containment of
ideals. -/
theorem not_zeroLocus_subset_iff {p q : Ideal A} [p.IsPrime] :
    ¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A) ↔
      ¬ q ≤ p := sorry

end ReesAlgebra
