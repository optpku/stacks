/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Base change of locally quasi-finite morphisms of algebraic spaces

Locally quasi-finite morphisms of algebraic spaces are stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyQuasiFinite

/-- Locally quasi-finite morphisms of algebraic spaces are stable under
pullback along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyQuasiFinite g) :
    LocallyQuasiFinite g' := sorry

/-- The base-change projection `pullback.snd f g` of a locally quasi-finite
morphism `f : X ⟶ Y` is locally quasi-finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyQuasiFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

/-- Locally quasi-finite morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyQuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

end LocallyQuasiFinite

/-- The second projection from a pullback of a locally quasi-finite morphism
of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [LocallyQuasiFinite f] [HasPullback f g] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
