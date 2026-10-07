module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.56.5: The Chern character is a canonical ring homomorphism from
vector-bundle `K₀` to the completed rational nonnegative Chow-cohomology ring. -/
@[stacks 0FEM] #check (AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p),
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      ChowCohomology.Nonnegative.RationalCompletion δ p)

/- On a vector-bundle generator, the ring homomorphism is the componentwise
Chern character. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter_of :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)),
    AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacterValue δ p classes E)
