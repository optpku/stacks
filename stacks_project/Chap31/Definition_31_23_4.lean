/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction.Pullback
import StacksCheckRecall

/-!
# Definition 31.23.4

The reusable meromorphic-function pullback API is owned by
`ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction.Pullback`.

@stack 02OT
-/

@[expose] public section

/- Definition 31.23.4
Pullbacks of meromorphic functions are defined for a morphism when every canonical denominator
section pulls back to a canonical denominator section on each nested open. -/
@[stacks 02OT] #check
  (AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined :
    {X Y : AlgebraicGeometry.LocallyRingedSpace} → (X ⟶ Y) → Prop)

#check @AlgebraicGeometry.LocallyRingedSpace.meromorphicFunctionDenominators
#check @AlgebraicGeometry.LocallyRingedSpace.mem_meromorphicFunctionDenominators_iff

@[stacks 02OT "section pullback on nested opens"]
#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackSection

#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksMeromorphicFunctionsDefined

#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined_iff
#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackSection_mem_regularSections
#check @AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackSection_mem_meromorphicFunctionDenominators
