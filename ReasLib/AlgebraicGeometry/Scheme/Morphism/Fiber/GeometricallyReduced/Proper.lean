/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Reduced
import Mathlib.Tactic.CrossRefAttribute

/-!
# Openness of geometrically reduced fibre loci

This module records openness of the geometrically reduced fibre locus for flat proper morphisms
of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat proper morphism of finite presentation, the locus in the target where the fibres
are geometrically reduced is open. -/
@[stacks 0C0E]
theorem isOpen_geometricallyReducedFiberLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsProper f] [FinitePresentation f] :
    IsOpen f.geometricallyReducedFiberLocus := sorry

end AlgebraicGeometry.Scheme.Hom
