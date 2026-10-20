/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
import Mathlib.Topology.Sets.Closeds
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open TopologicalSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (E : ModuleDerived X)
variable (T : Closeds (Points X))

/- Definition 75.3.2: `E` is supported on the closed subset `T` when all of its
cohomology sheaves are supported on `T`. -/
@[stacks 08GF] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsSupportedOn E (T : Set (Points X)) : Prop)

/- The canonical predicate is equivalent to the support condition in every cohomological degree. -/
#check isSupportedOn_iff E (T : Set (Points X))
