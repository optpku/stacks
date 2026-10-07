module

public import stacks_project.Chap111.Exercise_111_27_10_Kernel
public import stacks_project.Chap111.Exercise_111_27_10_StrictTransform
import Mathlib.Tactic.CrossRefAttribute

/-!
# Blowing up: Part III

This file records the four clauses of Exercise 111.27.10: surjectivity of the
canonical Rees quotient map, the induced bijection from
`ProjectiveSpectrum (Grading.grade (I.map (Ideal.Quotient.mk p)))` onto the
strict transform of `PrimeSpectrum.zeroLocus p`, the identification of that
strict transform with `ProjectiveSpectrum.zeroLocus` of
`Grading.strictTransformIdeal I p`, and the separation of incomparable prime
loci after blowing up `p + q`.
-/

@[expose] public section

noncomputable section

universe u

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- Exercise 111.27.10 (1): the canonical Rees map
`reesAlgebra I →+* reesAlgebra (I.map (Ideal.Quotient.mk p))` is surjective. -/
@[stacks 02EF]
theorem quotientMap_surjective (I p : Ideal A) :
    Function.Surjective (quotientMap I p) := sorry

end ReesAlgebra.Grading

namespace ReesAlgebra

variable {A : Type u} [CommRing A]

/-- Exercise 111.27.10 (2): the map on projective spectra induced by the Rees
quotient map is bijective onto the strict transform of
`PrimeSpectrum.zeroLocus p`. -/
@[stacks 02EF]
theorem quotientComap_bijOn_strictTransform (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    Set.BijOn (quotientComap I p) Set.univ
      (strictTransform I (PrimeSpectrum.zeroLocus (p : Set A))) := sorry

/-- Exercise 111.27.10 (3): the strict transform of `PrimeSpectrum.zeroLocus p`
equals `ProjectiveSpectrum.zeroLocus` of the homogeneous ideal `P` with
`P_d = I ^ d ∩ p`. -/
@[stacks 02EF]
theorem strictTransform_eq_zeroLocus (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      ProjectiveSpectrum.zeroLocus (Grading.grade I) (Grading.strictTransformIdeal I p) :=
  sorry

/-- Exercise 111.27.10 (4): if `p` and `q` are incomparable primes, blowing up
`I = p + q` separates the strict transforms of `PrimeSpectrum.zeroLocus p` and
`PrimeSpectrum.zeroLocus q`. -/
@[stacks 02EF]
theorem disjoint_strictTransform (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    Disjoint (strictTransform (p + q) (PrimeSpectrum.zeroLocus (p : Set A)))
      (strictTransform (p + q) (PrimeSpectrum.zeroLocus (q : Set A))) := sorry

end ReesAlgebra
