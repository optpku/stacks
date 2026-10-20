/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

open AlgebraicGeometry

universe u

variable (X : Scheme.{u})
variable (E : RingedSpace.ModuleDerived X.toLocallyRingedSpace.toRingedSpace)
variable (T : TopologicalSpace.Closeds X)

/- Definition 36.6.1: `E` is supported on the closed subset `T` when all of its
cohomology sheaves are supported on `T`. -/
@[stacks 08DA] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsSupportedOn E (T : Set X) : Prop)

/- The canonical predicate is equivalent to the support condition in every cohomological degree. -/
#check RingedSpace.ModuleDerived.isSupportedOn_iff E (T : Set X)
