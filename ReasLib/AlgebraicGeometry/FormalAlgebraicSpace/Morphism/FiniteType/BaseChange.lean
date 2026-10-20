/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of finite type and locally finite type morphisms of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType

/-- Locally of finite type morphisms of functors of points are stable under base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

/-- The base-change projection of a locally of finite type morphism is locally of finite type. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd
    (P := @LocallyOfFiniteType S) f g inferInstance

end AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Finite type morphisms of functors of points are stable under base change. -/
instance finiteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

namespace FiniteType

/-- The pullback of a finite type morphism in a cartesian square is of finite type. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : FiniteType g) : FiniteType g' := by
  exact MorphismProperty.of_isPullback (P := @FiniteType S) sq hg

/-- The base-change projection of a finite type morphism is of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : FiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    FiniteType (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := @FiniteType S) f g hf

end FiniteType

/-- The base-change projection of a finite type morphism is of finite type. -/
instance finiteType_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FiniteType f] [HasPullback f g] :
    FiniteType (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := @FiniteType S) f g inferInstance

namespace LocallyOfFiniteType

/-- The pullback of a locally finite type morphism in a cartesian square is locally
of finite type. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType g' := by
  exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType S) sq hg

/-- The base-change projection of a locally finite type morphism is locally of finite type. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (g : Z ⟶ Y) [HasPullback f g] :
    LocallyOfFiniteType (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := @LocallyOfFiniteType S) f g hf

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
