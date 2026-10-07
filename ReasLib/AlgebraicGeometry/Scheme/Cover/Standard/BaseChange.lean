module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard

/-!
# Base change of standard finite affine covers

This leaf records the stability of each of the five standard affine-cover
conditions under affine base change.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

namespace StandardTopology

/-- Pulling a standard finite affine cover back to an affine scheme produces
a standard cover for the same topology. -/
theorem IsCover.pullback {T T' : Scheme.{u}} [IsAffine T']
    (τ : StandardTopology) (family : AffineFamilyOver T) (g : T' ⟶ T)
    (hfamily : τ.IsCover family) :
    τ.IsCover (family.pullback g) := sorry

end StandardTopology

end

end AlgebraicGeometry
