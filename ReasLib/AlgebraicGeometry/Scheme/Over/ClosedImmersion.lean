/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The underlying morphism of the canonical map to an over-scheme is a closed
immersion whenever the given scheme morphism is a closed immersion. -/
instance overHomMkIsClosedImmersion
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left :=
  ‹IsClosedImmersion i›

/-- The underlying first projection of a pullback of schemes over a base is a
closed immersion when the underlying second morphism is a closed immersion. -/
instance overPullbackFstIsClosedImmersion
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion g.left] :
    IsClosedImmersion (pullback.fst f g).left := sorry

/-- Pulling back a closed immersion along a morphism to an over-object gives a
closed immersion on the underlying schemes. -/
instance (priority := 1100) overPullbackFstHomMkIsClosedImmersion
    {S : Scheme.{u}} {A X : Over S} {Z : Scheme.{u}}
    (f : A ⟶ Over.mk X.hom) (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion
      (pullback.fst f (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left := by
  refine @overPullbackFstIsClosedImmersion S A (Over.mk (i ≫ X.hom)) X f
    (Over.homMk i (by rfl)) ?_
  exact ‹IsClosedImmersion i›

end AlgebraicGeometry.Scheme
