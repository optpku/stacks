/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 36.37.5: for a quasi-compact and quasi-separated scheme with the resolution
property, the canonical exact functor from bounded finite locally free homotopy objects to
perfect derived objects factors through an exact equivalence after localizing at
quasi-isomorphisms. -/
@[stacks 0F8I] #check
  (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctor_isEquivalence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (_ : AlgebraicGeometry.Scheme.HasResolutionProperty X),
      (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctor X).IsEquivalence)

#check
  (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.toPerfect_isTriangulated :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.toPerfect X).IsTriangulated)

#check
  (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctorFacIso :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.quasiIso X).Q ⋙
          AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctor X ≅
        AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.toPerfect X)

#check
  (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctor_isTriangulated :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (AlgebraicGeometry.Scheme.BoundedFiniteLocallyFreeHomotopy.localizationFunctor X).IsTriangulated)
