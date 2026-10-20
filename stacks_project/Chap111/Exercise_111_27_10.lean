/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading.Quotient
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Quotient
import StacksCheckRecall

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

universe u

open AlgebraicGeometry

/- Exercise 111.27.10 (1): the Rees quotient map is surjective. -/
@[stacks 02EF] #check (ReesAlgebra.Grading.quotientMap_surjective :
  ∀ {A : Type u} [CommRing A] (I p : Ideal A),
    Function.Surjective (ReesAlgebra.Grading.quotientMap I p))

/- Exercise 111.27.10 (2): the quotient projective spectrum maps bijectively onto
the strict transform of the prime vanishing locus. -/
@[stacks 02EF] #check (ReesAlgebra.quotientComap_bijOn_strictTransform :
  ∀ {A : Type u} [CommRing A] (I p : Ideal A) [p.IsPrime],
    Set.BijOn (ReesAlgebra.quotientComap I p) Set.univ
      (ReesAlgebra.strictTransform I (PrimeSpectrum.zeroLocus (p : Set A))))

/- Exercise 111.27.10 (3): the homogeneous kernel has degree-`d` piece
`I ^ d ∩ p` and its zero locus is the strict transform. -/
@[stacks 02EF] #check (ReesAlgebra.strictTransform_eq_zeroLocus :
  ∀ {A : Type u} [CommRing A] (I p : Ideal A) [p.IsPrime],
    ReesAlgebra.strictTransform I (PrimeSpectrum.zeroLocus (p : Set A)) =
      ProjectiveSpectrum.zeroLocus (ReesAlgebra.Grading.grade I)
        (ReesAlgebra.Grading.strictTransformIdeal I p))

/- Exercise 111.27.10 (4): blowing up the sum of incomparable prime ideals
separates their strict transforms. -/
@[stacks 02EF] #check (ReesAlgebra.disjoint_strictTransform :
  ∀ {A : Type u} [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime],
    (¬ PrimeSpectrum.zeroLocus (p : Set A) ⊆ PrimeSpectrum.zeroLocus (q : Set A)) →
    (¬ PrimeSpectrum.zeroLocus (q : Set A) ⊆ PrimeSpectrum.zeroLocus (p : Set A)) →
    Disjoint (ReesAlgebra.strictTransform (p + q) (PrimeSpectrum.zeroLocus (p : Set A)))
      (ReesAlgebra.strictTransform (p + q) (PrimeSpectrum.zeroLocus (q : Set A))))
