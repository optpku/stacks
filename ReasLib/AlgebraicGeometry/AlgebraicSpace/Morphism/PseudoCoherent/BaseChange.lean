/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.BaseChange

/-!
# Flat base change of pseudo-coherent morphisms of algebraic spaces

Pseudo-coherent morphisms of algebraic spaces are preserved by base change
along a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PseudoCoherent

/-- Pseudo-coherent morphisms of algebraic spaces are stable under base change
along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Pseudo-coherent morphisms of algebraic spaces are stable under base change
along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {Y' Y : AlgebraicSpace S} (g : Y' ⟶ Y) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S)) g :=
  instIsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong g inferInstance

/-- The pullback of a pseudo-coherent morphism of algebraic spaces along a
flat morphism, expressed by an `IsPullback` square, is pseudo-coherent. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} [Flat f]
    (sq : IsPullback f' g' g f) (hg : PseudoCoherent g) :
    PseudoCoherent g' :=
  MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
    (P := (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S))) sq hg

/-- The base-change projection `pullback.snd f g` of a pseudo-coherent morphism
`f : X ⟶ Y` along a flat morphism `g` is pseudo-coherent. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [PseudoCoherent f] [Flat g] :
    PseudoCoherent (pullback.snd f g) :=
  MorphismProperty.pullback_snd
    (P := (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S))) f g inferInstance

end AlgebraicGeometry.AlgebraicSpace.PseudoCoherent
