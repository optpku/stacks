/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Morphism

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

/-- Scheme-theoretic fibres of finite-type separated morphisms over a Noetherian scheme are locally Noetherian. -/
instance instFiberIsLocallyNoetherian
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (y : Y.obj.left) :
    IsLocallyNoetherian (f.hom.left.fiber y) := sorry

end AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
