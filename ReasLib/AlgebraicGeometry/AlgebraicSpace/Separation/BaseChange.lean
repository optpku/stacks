/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Base change of separation properties for algebraic-space morphisms

Separated, locally separated, and quasi-separated morphisms of algebraic
spaces are stable under pullback and arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- The base change of a separated algebraic-space morphism in an arbitrary
pullback square is separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Separated g) : Separated g' := sorry

/-- The second projection from a pullback of a separated morphism is
separated. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Separated f) (g : Z ⟶ Y) [HasPullback f g] :
    Separated (pullback.snd f g) := sorry

end Separated

/-- The second projection from a pullback of a separated morphism is
separated when separatedness is available as an instance. -/
instance separated_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Separated f] [HasPullback f g] :
    Separated (pullback.snd f g) := sorry

namespace LocallySeparated

/-- The base change of a locally separated algebraic-space morphism in an
arbitrary pullback square is locally separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallySeparated g) :
    LocallySeparated g' := sorry

/-- The second projection from a pullback of a locally separated morphism is
locally separated. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallySeparated f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallySeparated (pullback.snd f g) := sorry

end LocallySeparated

/-- The second projection from a pullback of a locally separated morphism is
locally separated when local separatedness is available as an instance. -/
instance locallySeparated_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallySeparated f] [HasPullback f g] :
    LocallySeparated (pullback.snd f g) := sorry

namespace QuasiSeparated

/-- The base change of a quasi-separated algebraic-space morphism in an
arbitrary pullback square is quasi-separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiSeparated g) :
    QuasiSeparated g' := sorry

/-- The second projection from a pullback of a quasi-separated morphism is
quasi-separated. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiSeparated f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := sorry

end QuasiSeparated

/-- The second projection from a pullback of a quasi-separated morphism is
quasi-separated when quasi-separatedness is available as an instance. -/
instance quasiSeparated_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [QuasiSeparated f] [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := sorry

/-- Separatedness is stable under arbitrary base change. -/
instance separated_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Separated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Local separatedness is stable under arbitrary base change. -/
instance locallySeparated_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Quasi-separatedness is stable under arbitrary base change. -/
instance quasiSeparated_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace
