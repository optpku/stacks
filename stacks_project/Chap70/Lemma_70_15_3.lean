/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.Reduction
import StacksCheckRecall

/-!
# Lemma 70.15.3

If the reduction of an algebraic space is a scheme, then the algebraic space
itself is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.15.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `reduction X` is a scheme, then `X` is a scheme. -/
@[stacks 07VU] #check (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_reduction :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme (reduction X)], IsScheme X)
