module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ThreeQuadrics

@[expose] public section

universe u

/- Exercise 111.45.6: the possible Hilbert polynomials of cokernels of three
quadric equations on the projective plane over an arbitrary field. -/
@[stacks 0DCJ] #check
  (AlgebraicGeometry.ProjectiveSpace.threeQuadricCoker_hilbertPolynomial_classification :
    ∀ (k : Type u) [Field k] (P : ℤ → ℤ),
      (∃ (s : Fin 3 → MvPolynomial (Fin 3) k)
          (hs : ∀ i, s i ∈ AlgebraicGeometry.ProjectiveSpace.grading k 2 2),
        AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k 2
          (AlgebraicGeometry.ProjectiveSpace.threeQuadricCoker k s hs) = P) ↔
        ∃ j : Fin 9, P = AlgebraicGeometry.ProjectiveSpace.threeQuadricHilbertValues j)
