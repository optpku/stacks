/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.FiniteSeparablePoints
import StacksCheckRecall

/-!
# Lemma 72.16.2

Finite separable field-valued points are dense on an algebraic space smooth over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.16.2: let `k` be a field, and let `X` be an algebraic space smooth over
`Spec k`. The set of points of `X` which are images of morphisms `Spec k' ⟶ X` with
`k'/k` finite separable is dense in the space of points of `X`. -/
@[stacks 07W4] #check (AlgebraicGeometry.AlgebraicSpace.dense_finiteSeparableFieldPoints :
  ∀ {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Smooth (SchemeRealization.toBase X)],
    Dense (setOf fun x : Points X ↦ IsFiniteSeparableFieldPoint x))

end AlgebraicGeometry.AlgebraicSpace
