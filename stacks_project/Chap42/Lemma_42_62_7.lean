/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup

universe u

/- Lemma 42.62.7: For a quasi-compact smooth scheme over a field with affine diagonal,
the smooth intersection product agrees after tensoring with ℚ with the regular
intersection product on arbitrary rational Chow classes. -/
@[stacks 0FFF] #check
  (AlgebraicGeometry.ChowGroup.smoothIntersectionProductRational_eq_regularIntersectionProduct :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] [CompactSpace X.left]
      [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
      (α β : rationalChow (fun _ ↦ 0) X),
      smoothIntersectionProductRational X α β =
        regularIntersectionProduct (fun _ ↦ 0) X
          (ChernClass.Theory.canonical (fun _ ↦ 0) X.hom)
          (SchemeOverField.topologicalKrullDim_lt_top X) α β)

