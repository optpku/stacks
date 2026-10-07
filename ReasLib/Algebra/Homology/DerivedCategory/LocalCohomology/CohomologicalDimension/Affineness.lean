module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaum
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The complement of the zero locus of a finitely generated ideal with
local-cohomological dimension one is nonempty and affine. -/
theorem idealComplementOpens_isAffine_of_dimension_eq_one
    (I : Ideal A) (hI : I.FG) (hcd : dimension I hI = 1) :
    Nonempty (idealComplementOpens I) ∧ IsAffineOpen (idealComplementOpens I) := sorry

/-- In an excellent normal local ring of Krull dimension two, the complement
of the zero locus of an ideal whose quotient has Krull dimension at least one
is affine. -/
@[stacks 0EB7]
theorem idealComplementOpens_isAffine_of_ringKrullDim_eq_two
    {A : Type u} [CommRing A] [IsLocalRing A] [IsExcellentRing.{u, u} A]
    [IsNormalRing A] (I : Ideal A) (h_dimension : 1 ≤ ringKrullDim (A ⧸ I))
    (h_ringDimension : ringKrullDim A = 2) :
    IsAffineOpen (idealComplementOpens I) := sorry

end Ideal.LocalCohomology
