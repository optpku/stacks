/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Functor
import StacksCheckRecall

/-! # Predeformation functors and associated cofibered sets -/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/- Remark 90.6.3 (1): a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a
predeformation functor iff the associated cofibered set `CategoryOfElements.π F`
is a predeformation category. -/
@[stacks 06GT]
#check (CategoryTheory.Functor.isPredeformationFunctor_iff_isPredeformationCategory :
  (F : ArtinianLocalAlgCat Λ k ⥤ Type v) →
    CategoryTheory.Functor.IsPredeformationFunctor F ↔
      CategoryTheory.Functor.IsPredeformationCategory (CategoryOfElements.π F))

/- Remark 90.6.3 (2): if `p` is a predeformation category, then the functor of
isomorphism classes `opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op`
is a predeformation functor. -/
@[stacks 06GT]
#check (CategoryTheory.Functor.fiberIsoClassPresheaf_isPredeformationFunctor :
  {F : Type v} → [Category.{w} F] →
    (p : F ⥤ ArtinianLocalAlgCat Λ k) → [IsPredeformationCategory p] →
      CategoryTheory.Functor.IsPredeformationFunctor
        (opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op))

end CategoryTheory.Functor
