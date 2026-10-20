/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.BaseChange

/-!
# Base change of quasi-finite morphisms of algebraic spaces

Locally of finite type, locally quasi-finite morphisms and quasi-finite
morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Locally of finite type, locally quasi-finite morphisms of algebraic spaces
are stable under arbitrary base change. -/
instance locallyQuasiFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) := sorry

namespace QuasiFinite

/-- Quasi-finite morphisms of algebraic spaces are stable under pullback along
an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiFinite g) : QuasiFinite g' := sorry

/-- The base-change projection `pullback.snd f g` of a quasi-finite morphism
`f : X ⟶ Y` is quasi-finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiFinite (pullback.snd f g) := sorry

end QuasiFinite

/-- The second projection from a pullback of a quasi-finite morphism of
algebraic spaces is quasi-finite. -/
instance quasiFinite_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiFinite f] [HasPullback f g] :
    QuasiFinite (pullback.snd f g) := sorry

/-- Quasi-finite morphisms of algebraic spaces are stable under arbitrary
base change. -/
instance quasiFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace
