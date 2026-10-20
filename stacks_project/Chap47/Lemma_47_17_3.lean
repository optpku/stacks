module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.DimensionFunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.17.3: the normalization-degree function of a dualizing complex over a Noetherian
commutative ring is a dimension function on its prime spectrum. -/
@[stacks 0A7Z] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.isDimensionFunction :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
      {ω : DerivedCategory (ModuleCat.{u} A)},
      ω.IsDualizingComplex H →
      ∀ {δ : PrimeSpectrum A → ℤ},
        IsNormalizationDegreeFunction ω δ → IsDimensionFunction δ)

end CategoryTheory.DerivedCategory.IsDualizingComplex
