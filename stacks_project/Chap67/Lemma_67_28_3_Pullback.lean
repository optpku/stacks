module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Base change of finite-presentation morphisms of algebraic spaces

Finite-presentation morphisms and locally-of-finite-presentation morphisms of
algebraic spaces are stable under arbitrary base change. This module records
the morphism-level pullback companions for the existing `FinitePresentation`
and `LocallyOfFinitePresentation` classes from Definition 67.28.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → FinitePresentation g → FinitePresentation g')

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    FinitePresentation f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      FinitePresentation (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.finitePresentation_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [FinitePresentation f] → [HasPullback f g] →
      FinitePresentation (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → LocallyOfFinitePresentation g → LocallyOfFinitePresentation g')

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    LocallyOfFinitePresentation f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      LocallyOfFinitePresentation (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [LocallyOfFinitePresentation f] → [HasPullback f g] →
      LocallyOfFinitePresentation (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
