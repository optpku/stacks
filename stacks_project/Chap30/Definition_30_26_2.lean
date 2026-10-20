/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
variable (Z : TopologicalSpace.Closeds X)

/- Definition 30.26.2 [0CYM]: The equivalent conditions of
`ClosedSubset.isProperOver_tfae` define when `Z` is proper over `S`; equivalently, the
canonical reduced induced closed subscheme on `Z` is proper over `S`. -/
@[stacks 0CYM] #check (AlgebraicGeometry.ClosedSubset.IsProperOver f Z : Prop)

end AlgebraicGeometry
