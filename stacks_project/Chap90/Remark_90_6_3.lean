module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor

/-!
# Predeformation functors and associated cofibered sets

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a predeformation functor iff
the associated cofibered set `CategoryOfElements.π F` is a predeformation category.
If `p` is a predeformation category, then
`opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op` is a predeformation
functor.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A predeformation category is cofibered in groupoids over `ArtinianLocalAlgCat Λ k`. -/
instance isFiberedInGroupoids_op
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] :
    IsFibered.InGroupoids p.op := sorry

/-- Remark 90.6.3 (1): a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a
predeformation functor iff the associated cofibered set `CategoryOfElements.π F`
is a predeformation category. -/
@[stacks 06GT]
theorem isPredeformationFunctor_iff_isPredeformationCategory
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsPredeformationFunctor F ↔ IsPredeformationCategory (CategoryOfElements.π F) :=
  sorry

/-- Remark 90.6.3 (2): if `p` is a predeformation category, then the functor of
isomorphism classes `opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op`
is a predeformation functor. -/
@[stacks 06GT, instance]
instance fiberIsoClassPresheaf_isPredeformationFunctor
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] :
    IsPredeformationFunctor
      (opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op) := sorry

end CategoryTheory.Functor
