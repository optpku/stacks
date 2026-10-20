/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
import StacksCheckRecall

@[expose] public section

/- Definition 20.26.14 core recall: the reusable fixed-right derived tensor owner is the
ReasLib ringed-space facade.  This compatibility file exports no chapter-local quotient lift. -/

open AlgebraicGeometry CategoryTheory ComplexShape

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)]
variable (L : ModuleDerived X)

@[stacks 06YH "fixed-right derived tensor core owner"]
#check @derivedTensorProduct

#check @derivedTensorSourceFunctor
#check @derivedTensorProductCounit
#check @derivedTensorProduct_isLeftDerivedFunctor

end AlgebraicGeometry.RingedSpace

end
