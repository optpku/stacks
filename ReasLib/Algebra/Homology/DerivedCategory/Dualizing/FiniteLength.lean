module

public import ReasLib.Algebra.Category.ModuleCat.FiniteLength
public import ReasLib.Algebra.Module.MatlisDuality.Duality
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a normalized dualizing complex over a Noetherian local ring, derived internal-Hom
dualization on finite-length modules is naturally isomorphic to Matlis dualization into an
injective hull concentrated in degree zero. -/
theorem finiteLengthRHomIsoMatlisDual
    (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull) :
    Nonempty
      (((((Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).ι ⋙
          ModuleCat.single0Functor).op) ⋙
            (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω) ≅
        ((Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).ι.op ⋙
          (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} A)).dualFunctor
            (ModuleCat.of A E) ⋙ ModuleCat.single0Functor)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
