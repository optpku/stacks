/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.H
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Site

/- Example 38.35.1: if a surjective closed immersion of finite presentation between affine
schemes is not an isomorphism, then the global-sections structure presheaf fails the sheaf
condition on its singleton h covering. -/
@[stacks 0EV0] #check
  (AlgebraicGeometry.Scheme.Site.structurePresheaf_not_isSheafFor_hCover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsAffine X] [IsAffine Y] [Surjective f] [IsClosedImmersion f]
      [Hom.FinitePresentation f] (_ : ¬ IsIso f),
      ¬ Presieve.IsSheafFor
        (structurePresheaf (Functor.id Scheme.{u}) ⋙ CategoryTheory.forget RingCat.{u})
        (Presieve.singleton f))

end AlgebraicGeometry.Scheme.Site
