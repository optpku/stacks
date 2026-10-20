/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange

/-!
# Pullback companions for immersions of algebraic spaces

Typed compatibility checks for the shared base-change API and the canonical
closed- and open-immersion pullback-square lemmas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → IsImmersion g → IsImmersion g')

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    IsImmersion f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      IsImmersion (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsImmersion f] [HasPullback f g], IsImmersion (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y U P : AlgebraicSpace S}
    {f : Y ⟶ X} {ι : U ⟶ X} {pY : P ⟶ Y} {pU : P ⟶ U} [IsClosedImmersion ι],
    IsPullback pY pU f ι → IsClosedImmersion pY)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    IsClosedImmersion f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      IsClosedImmersion (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsClosedImmersion f] [HasPullback f g], IsClosedImmersion (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y U P : AlgebraicSpace S}
    {f : Y ⟶ X} {ι : U ⟶ X} {pY : P ⟶ Y} {pU : P ⟶ U} [IsOpenImmersion ι],
    IsPullback pY pU f ι → IsOpenImmersion pY)

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    IsOpenImmersion f → ∀ (g : Z ⟶ Y) [HasPullback f g],
      IsOpenImmersion (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion f] [HasPullback f g], IsOpenImmersion (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
