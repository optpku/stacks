/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    x ∈ openAway I ↔ ¬ I ≤ x.asIdeal := sorry

/-- The homogeneous kernel determines a relevant prime over `p` when the
center is not contained in `p`. -/
def genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ProjectiveSpectrum (Grading.grade I) where
  asHomogeneousIdeal := Grading.strictTransformIdeal I p
  isPrime := Grading.isPrime_toIdeal_strictTransformIdeal I p
  not_irrelevant_le := Grading.not_irrelevant_le_strictTransformIdeal I p hI

/-- The homogeneous ideal of the lift of `p` is the kernel of the Rees quotient. -/
theorem genericLift_asHomogeneousIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (genericLift I p hI).asHomogeneousIdeal = Grading.strictTransformIdeal I p := sorry

/-- The contraction of the lifted prime to the base ring is `p`. -/
theorem genericLift_liesOver (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    (toSpec I (genericLift I p hI)).asIdeal = p := sorry

/-- A relevant homogeneous prime over `p` equals its canonical lift. -/
theorem genericLift_unique (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p)
    (x : ProjectiveSpectrum (Grading.grade I))
    (hx : (toSpec I x).asIdeal = p) : x = genericLift I p hI := sorry

/-- The lifted generic prime belongs to the strict transform of `V(p)`. -/
theorem genericLift_mem_strictTransform (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    genericLift I p hI ∈ strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) := sorry

/-- The strict transform of `V(p)` is the closure of its lifted generic point
when the center does not contain that generic point. -/
theorem strictTransform_eq_closure_genericLift (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      closure {genericLift I p hI} := sorry

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
      HomogeneousIdeal.comap (Grading.quotientGradedMap I p) x.asHomogeneousIdeal := sorry

/-- If `q` is not contained in `p`, their sum is not contained in `p`. -/
theorem not_add_le_of_not_le {p q : Ideal A} (h : ¬ q ≤ p) : ¬ p + q ≤ p := sorry

/-- For prime `p`, non-containment of vanishing loci is equivalent to
non-containment of the defining ideals in the reverse direction. -/
theorem not_zeroLocus_subset_iff {p q : Ideal A} [p.IsPrime] :
    ¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A) ↔
      ¬ q ≤ p := sorry

/-- The projective spectrum of the quotient Rees algebra maps bijectively
onto the strict transform of the prime vanishing locus. -/
theorem quotientComap_bijOn_strictTransform (I p : Ideal A) [p.IsPrime] :
    Set.BijOn (quotientComap I p) Set.univ
      (strictTransform I (PrimeSpectrum.zeroLocus (p : Set A))) := sorry

/-- The strict transform of `V(p)` is the projective zero locus of the
homogeneous kernel with degree-`d` piece `I ^ d ∩ p`. -/
theorem strictTransform_eq_zeroLocus (I p : Ideal A) [p.IsPrime] :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      ProjectiveSpectrum.zeroLocus (Grading.grade I) (Grading.strictTransformIdeal I p) :=
  sorry

/-- Blowing up `p + q` separates the strict transforms of two incomparable
prime vanishing loci. -/
theorem disjoint_strictTransform (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hpq : ¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A))
    (hqp : ¬ PrimeSpectrum.zeroLocus (q : Set A) ⊆ PrimeSpectrum.zeroLocus (p : Set A)) :
    Disjoint (strictTransform (p + q) (PrimeSpectrum.zeroLocus (p : Set A)))
      (strictTransform (p + q) (PrimeSpectrum.zeroLocus (q : Set A))) := sorry

end ReesAlgebra
