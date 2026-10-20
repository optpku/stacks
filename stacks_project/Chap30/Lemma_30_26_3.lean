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

/- Lemma 30.26.3: if `Y ⊆ Z ⊆ X` are closed subsets and `Z` is proper over `S`, then `Y` is
proper over `S`. -/
@[stacks 0CYN] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.mono :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.LocallyOfFiniteType f] {Y Z : TopologicalSpace.Closeds X},
      Y ≤ Z → [AlgebraicGeometry.ClosedSubset.IsProperOver f Z] →
        AlgebraicGeometry.ClosedSubset.IsProperOver f Y)
