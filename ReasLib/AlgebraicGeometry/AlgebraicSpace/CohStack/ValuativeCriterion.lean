/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism

/-!
# Valuative existence for the stack of coherent sheaves

If `f : X ⟶ B` is proper and of finite presentation, then the structure
morphism of the stack of coherent sheaves satisfies the existence part of the
valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The structure morphism of the coherent-sheaf stack of a proper morphism of
finite presentation satisfies the existence part of the valuative criterion. -/
instance instExistence_forget (f : X ⟶ B) [FinitePresentation f] [Proper f] :
    Existence (forget f) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
