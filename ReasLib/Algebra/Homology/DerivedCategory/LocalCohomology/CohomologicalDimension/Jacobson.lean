module

public import Mathlib.RingTheory.Jacobson.Radical
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.NoetherianRestriction
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.KrullDimension

@[expose] public section

universe u

namespace Ideal.LocalCohomology

/-- If `I ≤ I' ≤ Ring.jacobson A` in a Noetherian ring of dimension `d`, then
the local-cohomological dimension of `I'` being less than `d` implies the same
strict bound for `I`. -/
theorem dimension_lt_of_le_of_le_ringJacobson {A : Type u} [CommRing A]
    [IsNoetherianRing A] (d : ℕ) (hdim : ringKrullDim A = d) (I I' : Ideal A)
    (h_le : I ≤ I') (h_jacobson : I' ≤ Ring.jacobson A)
    (h_cd : dimension I' I'.fg_of_isNoetherianRing < (d : ℤ)) :
    dimension I I.fg_of_isNoetherianRing < (d : ℤ) := sorry

end Ideal.LocalCohomology
