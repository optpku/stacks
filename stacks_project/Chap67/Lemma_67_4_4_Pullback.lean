/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Separated.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → Separated g → Separated g')
#check (AlgebraicGeometry.AlgebraicSpace.Separated.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    Separated f → (g : Z ⟶ Y) → [HasPullback f g] →
      Separated (pullback.snd f g))
#check (AlgebraicGeometry.AlgebraicSpace.separated_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Separated f] [HasPullback f g], Separated (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → LocallySeparated g → LocallySeparated g')
#check (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    LocallySeparated f → (g : Z ⟶ Y) → [HasPullback f g] →
      LocallySeparated (pullback.snd f g))
#check (AlgebraicGeometry.AlgebraicSpace.locallySeparated_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallySeparated f] [HasPullback f g],
    LocallySeparated (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → QuasiSeparated g → QuasiSeparated g')
#check (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    QuasiSeparated f → (g : Z ⟶ Y) → [HasPullback f g] →
      QuasiSeparated (pullback.snd f g))
#check (AlgebraicGeometry.AlgebraicSpace.quasiSeparated_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [QuasiSeparated f] [HasPullback f g],
    QuasiSeparated (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
