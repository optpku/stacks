module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteLength

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- Over a zero-dimensional Noetherian local ring, a normalized dualizing complex is
isomorphic to an injective hull of the residue field concentrated in degree zero. -/
theorem isoSingleInjectiveHull_of_ringKrullDim_eq_zero
    (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (hdim : ringKrullDim A = 0)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull) :
    Nonempty (ω ≅ ModuleCat.single0 (ModuleCat.of A E)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
