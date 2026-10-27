/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The relative Picard functor of a flat, finitely presented, proper morphism
preserving the structure sheaf after every scheme-valued base change is smooth
over the base when the morphism has relative dimension at most one. -/
theorem isSmoothOver (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] [RelativeDimensionLE f 1] :
    IsSmoothOver (picardFunctor f).obj := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
