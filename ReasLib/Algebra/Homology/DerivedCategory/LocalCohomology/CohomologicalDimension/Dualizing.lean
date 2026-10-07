module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.TopDimension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/-- For a Noetherian local ring with a normalized dualizing complex, degree-zero
local cohomology vanishing for an ideal forces its local-cohomological dimension
to be strictly smaller than the Krull dimension of the ring. -/
theorem dimension_lt_ringKrullDim_of_degreeZero_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (comparison : CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex comparison.closed) (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (h_vanish : IsZero
      ((homologyFunctor (ModuleCat A) 0).obj (RΓ.obj ω).obj)) :
    (dimension I I.fg_of_isNoetherianRing : EInt) <
      WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A) := sorry

end Ideal.LocalCohomology
