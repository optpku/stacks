/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Regularity
import StacksCheckRecall

/-!
# Lemma 72.16.1

An algebraic space smooth over a field is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 72.16.1: let `k` be a field, and let `X` be an algebraic space smooth over `k`.
Then `X` is a regular algebraic space. -/
@[stacks 06M1] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegular_of_smooth_over_field :
    ∀ {k : Type u} [Field k]
      {X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of k))}
      [AlgebraicGeometry.AlgebraicSpace.Smooth
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)],
      AlgebraicGeometry.AlgebraicSpace.IsRegular X)
