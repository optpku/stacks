module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Compatibility bridge for Chapter 42 files importing the Chern-character component. -/
#check
  (AlgebraicGeometry.ChernClass.Theory.characterComponent :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      TensorProduct ℤ (AlgebraicGeometry.ChowCohomology.Nonnegative.degree δ p i) ℚ)
