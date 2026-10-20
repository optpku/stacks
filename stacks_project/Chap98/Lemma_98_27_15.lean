/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Smooth
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidsOver
open FiberedCategoryOver Opposite TopologicalSpace
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 98.27.15. An adic morphism from a scheme completion that is versal
at a closed point is smooth after restricting to one open neighbourhood. -/
@[stacks 0GI9] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.exists_isSmooth_nhd :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian W] (R : ReductionData W)
    [AlgebraicSpace.LocallyOfFiniteType (AlgebraicSpace.SchemeRealization.toBase R.space)]
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W)
    (hg : representableByAlgebraicSpaces g) (v : V.left) (hv : IsClosed {v})
    [IsFiniteTypePoint v] [IsVersalAt Z g v],
    ∃ V' : V.left.Opens,
      v ∈ V' ∧
        representableByAlgebraicSpaces (restrictAlong Z V' ≫ g) ∧
          ∀ (ha : representableByAlgebraicSpaces (restrictAlong Z V' ≫ g))
            ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ W),
            AlgebraicSpace.Smooth (ha.pullbackHom ξ))
