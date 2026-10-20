/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite

/-!
# Relative dimension of finite locally free morphisms

This file records the relative dimension of finite locally free scheme morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A finite locally free morphism has relative dimension zero. -/
instance instRelativeDimensionZeroOfIsFiniteLocallyFree
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsFiniteLocallyFree f] :
    Scheme.Hom.RelativeDimension f 0 := sorry

end AlgebraicGeometry
