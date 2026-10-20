/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Tor independence under vertical composition

Tor independence for two stacked cartesian squares implies Tor independence
for the outer rectangle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Tor independence for two stacked cartesian squares implies Tor independence
for their outer rectangle. -/
theorem torIndependentOver_verticalComposition {S : Scheme.{u}}
    {X' X Y' Y Z' Z : AlgebraicSpace S}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (top : IsPullback k f' f l) (bottom : IsPullback l g' g m)
    (hTop : TorIndependentOver (Over.mk f) (Over.mk l))
    (hBottom : TorIndependentOver (Over.mk g) (Over.mk m)) :
    TorIndependentOver (Over.mk (f ≫ g)) (Over.mk m) := sorry

/-- Tor independence for adjacent cartesian squares implies Tor independence for
their outer rectangle. -/
theorem torIndependentOver_horizontalComposition {S : Scheme.{u}}
    {X'' X' X Y'' Y' Y : AlgebraicSpace S}
    (g' : X'' ⟶ X') (g : X' ⟶ X)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    (left : IsPullback g' f'' f' h') (right : IsPullback g f' f h)
    (hTorRight : TorIndependentOver (Over.mk f) (Over.mk h))
    (hTorLeft : TorIndependentOver (Over.mk f') (Over.mk h')) :
    TorIndependentOver (Over.mk f) (Over.mk (h' ≫ h)) := sorry

end AlgebraicGeometry.AlgebraicSpace
