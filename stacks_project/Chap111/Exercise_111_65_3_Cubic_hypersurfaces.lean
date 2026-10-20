module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Cubic
public import Mathlib.Data.Complex.Basic
import StacksCheckRecall

/- Exercise 111.65.3 (Cubic hypersurfaces) (1): the complex vector space of all
triples has dimension `3 * (n + 1)`. -/
@[stacks 0GYB] #check
  (AlgebraicGeometry.ProjectiveSpace.Cubic.finrank_triples :
    ∀ n : ℕ, Module.finrank ℂ (Fin 3 → (Fin (n + 1) → ℂ)) = 3 * (n + 1))

/- Exercise 111.65.3 (Cubic hypersurfaces) (2): a homogeneous cubic in three
variables has ten coefficients, giving ten scalar equations for condition (*). -/
@[stacks 0GYB] #check
  (AlgebraicGeometry.ProjectiveSpace.Cubic.finrank_homogeneousCubic :
    Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 3) = 10)

/- Exercise 111.65.3 (Cubic hypersurfaces) (3): subtracting the ten equations from
the triple-space dimension gives the expected dimension `3 * n - 7`. -/
@[stacks 0GYB] #check
  (AlgebraicGeometry.ProjectiveSpace.Cubic.expectedDim_eq :
    ∀ n : ℕ, (3 * (n + 1) : ℤ) - 10 = 3 * (n : ℤ) - 7)

/- Exercise 111.65.3 (Cubic hypersurfaces) (4): for `1 ≤ n`, the locus of dependent
complex triples has topological Krull dimension `2 * n + 4`. -/
@[stacks 0GYB] #check
  (AlgebraicGeometry.ProjectiveSpace.Cubic.topologicalKrullDim_dependentLocus :
    ∀ {n : ℕ}, 1 ≤ n →
      topologicalKrullDim (AlgebraicGeometry.ProjectiveSpace.Cubic.dependentLocus ℂ n) =
        2 * n + 4)

/- Exercise 111.65.3 (Cubic hypersurfaces) (5): the expected dimension exceeds the
dependent-locus dimension exactly when `12 ≤ n`, so one expects a projective
plane on the cubic for `n ≥ 12`. This comparison is not an existence theorem. -/
@[stacks 0GYB] #check
  (AlgebraicGeometry.ProjectiveSpace.Cubic.expectedDim_gt_dependentDim_iff :
    ∀ {n : ℕ}, ((3 * (n + 1) : ℤ) - 10 > (2 * n + 4 : ℤ)) ↔ 12 ≤ n)
