/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects

/-!
# Limit preservation for finite Hilbert stacks

The canonical finite Hilbert forgetful morphism is limit preserving on objects
when the original morphism is representable by algebraic spaces and locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom renaming LocallyOfFinitePresentation → GroupoidLocallyOfFinitePresentation
open AlgebraicGeometry.Groupoids.Hom renaming LimitPreservingOnObjects → GroupoidLimitPreservingOnObjects
open CategoryTheory.StackOver.Groupoids.Hom (toGroupoidsMor)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- If a morphism of stacks in groupoids over `(Sch/S)_fppf` is representable by
algebraic spaces and locally of finite presentation, its finite Hilbert forgetful
morphism is limit preserving on objects for every natural degree. The finite
locally free descent argument is independent of the rank, so this includes
degree zero. -/
@[stacks 06CH]
instance forgetToY.limitPreservingOnObjects (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [GroupoidLocallyOfFinitePresentation (toGroupoidsMor F)] :
    GroupoidLimitPreservingOnObjects (toGroupoidsMor (forgetToY F d)) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
