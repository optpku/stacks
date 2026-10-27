/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Smoothness of the Picard structure morphism
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Smooth → GroupoidSmooth
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat, finitely presented, proper morphism of algebraic spaces of relative
dimension at most one, the Picard stack structure morphism is smooth. -/
instance toBase.smooth (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] [RelativeDimensionLE f 1] : GroupoidSmooth (toBase f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
