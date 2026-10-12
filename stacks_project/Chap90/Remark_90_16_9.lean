/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_10_5_Associated
public import stacks_project.Chap90.Remark_90_16_9_DeformationFunctor
public import stacks_project.Chap90.Remark_90_6_3

/-!
# Deformation functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a deformation functor when the
associated cofibered set is a deformation category. If `p` is a deformation
category, then `isoClassFunctor p` is a predeformation functor, but it is a
deformation functor only when that associated cofibered set also satisfies (RS).
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Remark 90.16.9 (1): a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a
deformation functor iff the associated cofibered set `CategoryOfElements.π F` is a
deformation category. -/
@[stacks 06JA]
theorem isDeformationFunctor_iff_isDeformationCategory
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsDeformationFunctor F ↔ IsDeformationCategory (CategoryOfElements.π F) :=
  sorry

/-- Remark 90.16.9 (2): if `p` is a deformation category, then the associated functor
of isomorphism classes `isoClassFunctor p` is a predeformation functor. -/
@[stacks 06JA, instance]
instance instIsPredeformationFunctor_isoClassFunctor
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsDeformationCategory p] :
    IsPredeformationFunctor (isoClassFunctor p) := sorry

/-- Remark 90.16.9 (3): if `p` is a deformation category, then `isoClassFunctor p` is
a deformation functor iff the associated cofibered set of `isoClassFunctor p`
satisfies (RS). Lemma 90.16.7 identifies this extra (RS) condition. -/
@[stacks 06JA]
theorem isoClassFunctor_isDeformationFunctor_iff
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsDeformationCategory p] :
    IsDeformationFunctor (isoClassFunctor p) ↔
      HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)) :=
  sorry

end CategoryTheory.Functor
