/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Ampleness and finite morphisms of algebraic spaces

Finite surjective pullback preserves and reflects scheme representability together with
ampleness of invertible modules on algebraic spaces proper over a Noetherian affine base.
-/

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- An invertible module on an algebraic space proper over a Noetherian ring is ample
on a scheme if and only if its pullback along a finite surjective morphism from another
proper algebraic space is ample on a scheme. -/
@[stacks 0GFB]
theorem isSchemeAndAmple_iff_pullback_of_isFinite_surjective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple L ↔ isSchemeAndAmple ((pullback f).obj L) :=
  sorry

/-- Finite surjective pullback between algebraic spaces proper over a Noetherian ring
preserves scheme representability together with ampleness of an invertible module. -/
theorem pullback_isSchemeAndAmple
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple L → isSchemeAndAmple ((pullback f).obj L) :=
  (isSchemeAndAmple_iff_pullback_of_isFinite_surjective πX πY f L).mp

/-- Scheme representability together with ampleness of an invertible module descends
along a finite surjective morphism between algebraic spaces proper over a Noetherian ring. -/
theorem isSchemeAndAmple_of_pullback
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple ((pullback f).obj L) → isSchemeAndAmple L :=
  (isSchemeAndAmple_iff_pullback_of_isFinite_surjective πX πY f L).mpr

end AlgebraicGeometry.AlgebraicSpace.Modules
