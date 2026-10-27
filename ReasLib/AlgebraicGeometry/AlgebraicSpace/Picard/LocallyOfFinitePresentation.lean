/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation

/-!
# Local finite presentation of the Picard structure morphism
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat, proper morphism `f : X ⟶ B` of finite presentation, the
Picard stack structure morphism over `B` is locally of finite presentation. -/
instance toBase.locallyOfFinitePresentation (f : X ⟶ B) [Flat f]
    [FinitePresentation f] [Proper f] :
    CohStack.Hom.LocallyOfFinitePresentation (toBase f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
