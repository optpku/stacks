/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
variable (T : TopologicalSpace.Closeds (Points X))

/- Definition 75.7.2: the closed subset `T` is proper over `Y` when it is the
existence of a closed-subspace structure proper over `Y`, expressed by a closed
immersion with point image `T` and proper composite. Under the stated
locally-of-finite-type hypothesis, this is equivalent to the reduced and
universal closed-subspace conditions of Lemma 75.7.1. -/
@[stacks 0CZD] #check (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f T : Prop)

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
