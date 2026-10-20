/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor
import StacksCheckRecall

/-!
# Deformation functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a deformation functor when the
associated cofibered set is a deformation category. If `p` is a deformation
category, then `isoClassFunctor p` is a predeformation functor, but not necessarily
a deformation functor: its associated cofibered set must also satisfy (RS).
Lemma 90.16.7 identifies this extra (RS) condition.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

open CategoryTheory.Functor

/- Remark 90.16.9 (1): a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a
deformation functor iff the associated cofibered set `CategoryOfElements.π F` is a
deformation category. -/
@[stacks 06JA] #check
  (CategoryTheory.Functor.isDeformationFunctor_iff_isDeformationCategory :
    ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v),
      IsDeformationFunctor F ↔ IsDeformationCategory (CategoryOfElements.π F))

variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [IsDeformationCategory p]

/- Remark 90.16.9 (2): if `p` is a deformation category, then the associated functor
of isomorphism classes `isoClassFunctor p` is a predeformation functor. -/
@[stacks 06JA] #check (CategoryTheory.Functor.instIsPredeformationFunctor_isoClassFunctor p :
  IsPredeformationFunctor (isoClassFunctor p))

/- Remark 90.16.9 (3): if `p` is a deformation category, then `isoClassFunctor p` is
a deformation functor iff the associated cofibered set of `isoClassFunctor p`
satisfies (RS). Lemma 90.16.7 identifies this extra (RS) condition. -/
@[stacks 06JA] #check (CategoryTheory.Functor.isoClassFunctor_isDeformationFunctor_iff p :
  IsDeformationFunctor (isoClassFunctor p) ↔
    HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)))
