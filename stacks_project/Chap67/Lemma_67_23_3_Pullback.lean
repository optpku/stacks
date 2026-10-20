module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange

/-!
# Base change of finite-type morphisms of algebraic spaces

Finite-type morphisms and locally-of-finite-type morphisms of algebraic spaces
are stable under arbitrary base change. This module checks the morphism-level
pullback companions for the existing `FiniteType` and `LocallyOfFiniteType` classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → FiniteType g → FiniteType g')

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    FiniteType f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      FiniteType (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.finiteType_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [FiniteType f] [HasPullback f g],
    FiniteType (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → LocallyOfFiniteType g → LocallyOfFiniteType g')

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    LocallyOfFiniteType f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      LocallyOfFiniteType (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType f] [HasPullback f g],
    LocallyOfFiniteType (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
