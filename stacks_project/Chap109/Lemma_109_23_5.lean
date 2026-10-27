/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stabilization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.23.5 -/
@[stacks 0E8B] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_stabilization :
    ∀ (g : ℕ), 2 ≤ g → ∀ (S : Scheme.{u}),
      ∃ F : ofObjectProperty (prestableOfGenus g S) ⟶
          ofObjectProperty (stableOfGenus g S),
        IsStabilization F)
