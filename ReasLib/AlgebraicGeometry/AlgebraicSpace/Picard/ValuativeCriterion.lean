/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion

/-!
# Valuative existence for the Picard structure morphism
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat, finitely presented, proper, smooth morphism of algebraic spaces,
the Picard structure morphism satisfies the existence part of the valuative
criterion, allowing dominating extensions of valuation rings. -/
instance toBase.existence (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Smooth f] : Existence (toBase f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
