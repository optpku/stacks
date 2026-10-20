/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
import StacksCheckRecall

@[expose] public section

/- Definition 17.25.1 (01CS), invertible clause: invertibility is the canonical property of an
object whose tensor-left functor is an equivalence. -/
@[stacks 01CS "invertible"]
#check @CategoryTheory.MonoidalCategory.isInvertibleObject

/- Definition 17.25.1 (01CS), trivial clause: a module is trivial when it is isomorphic to the
tensor unit, i.e. the structure module. -/
@[stacks 01CS "trivial"]
#check @AlgebraicGeometry.RingedSpace.IsTrivial

#check @AlgebraicGeometry.RingedSpace.unit_isTrivial
#check @CategoryTheory.MonoidalCategory.isInvertibleObject.iff_tensorRight
