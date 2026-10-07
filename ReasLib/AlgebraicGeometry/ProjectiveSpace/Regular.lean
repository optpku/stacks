module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Regularity of projective spaces
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Standard projective space over a field is regular. -/
theorem regularScheme (k : Type u) [Field k] (n : ℕ) :
    Scheme.Regular (scheme k n) :=
  @Scheme.Hom.regular_of_smooth_over_field k _ (scheme k n) (toSpec k n)
    (AlgebraicGeometry.instSmoothOfSmoothVariety (schemeOver k n))

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Projective space of a finite-dimensional vector space over a field is regular. -/
instance instRegularScheme : Scheme.Regular (scheme k V) := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
