/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Correspondence.Monoidal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 45.3.8: the projection-pullback/intersection tensor product on degree-zero
correspondences makes the category of smooth projective schemes over `k` symmetric monoidal,
with tensor unit represented by `Spec(k)`. -/
@[stacks 0FG7] #check (AlgebraicGeometry.Correspondence.instSymmetricCategory :
  ∀ {k : Type u} [Field k],
    SymmetricCategory (AlgebraicGeometry.Correspondence.Category k))

/- The concrete monoidal instance uses `Spec(k)` over itself as its tensor unit. -/
#check (AlgebraicGeometry.Correspondence.Category.scheme_unit :
  ∀ (k : Type u) [Field k],
    (AlgebraicGeometry.Correspondence.Category.unit k).scheme =
      AlgebraicGeometry.SchemeOverField.point k)
