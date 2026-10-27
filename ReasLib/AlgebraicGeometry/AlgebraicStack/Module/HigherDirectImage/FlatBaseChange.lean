/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Lifted
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange

/-!
# Flat base change of étale higher direct images
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Étale higher direct images of locally quasi-coherent modules with flat
base change along a quasi-compact and quasi-separated morphism of algebraic
stacks have flat base change. Higher direct images use enlarged coefficients,
so their flat base change property is expressed by the lifted comparisons. -/
@[stacks 0765]
instance hasFlatBaseChange_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F]
    [HasFlatBaseChange F] (i : ℕ) :
    HasFlatBaseChangeLift Y (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
