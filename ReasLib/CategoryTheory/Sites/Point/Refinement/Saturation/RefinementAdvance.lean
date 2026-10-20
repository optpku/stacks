/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Hom

/-!
# One-step advances of finite-cover refinement stages

This leaf packages a uniform refinement that realizes every finite-cover
request at the current target without choosing a presheaf or a pair of fiber
elements.  The separating `Saturation.Advance` remains the specialization for
arguments that must preserve a chosen inequality.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace RefinementStage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

/-- A uniform one-step finite-cover saturation choice with no chosen separating data.
It is intentionally an endomorphic, single-index-universe sequential API; heterogeneous target
refinements are represented by `Target.Hom` and directed target diagrams instead. -/
structure Advance where
  /-- The chosen further finite-cover refinement stage. -/
  next : RefinementStage.{u, v, q, r, r'} S → RefinementStage.{u, v, q, r, r'} S
  /-- The compatible refinement into the chosen further stage. -/
  hom : ∀ A : RefinementStage.{u, v, q, r, r'} S, Hom A (next A)
  /-- Every source-target request is realized after the chosen further refinement. -/
  realizes : ∀ A : RefinementStage.{u, v, q, r, r'} S, (hom A).realizesAll (J := J)

namespace Advance

/-- Two unseparated advances agree when their chosen successor stages and
successor refinements agree.  The realization field is proof-valued. -/
@[ext]
theorem ext
    {advance advance' : Advance.{u, v, q, r, r'} (J := J) (S := S)}
    (h_next : advance.next = advance'.next)
    (h_hom : HEq advance.hom advance'.hom) :
    advance = advance' := sorry

/-- Assemble an unseparated advance from a stagewise existence statement.  The chosen data are
encapsulated here, while `toExists` is the public specification for consumers. -/
noncomputable def ofExists
    (existsNext :
      ∀ A : RefinementStage.{u, v, q, r, r'} S,
        ∃ B : RefinementStage.{u, v, q, r, r'} S,
          ∃ f : Hom A B, f.realizesAll (J := J)) :
    Advance (J := J) (S := S) where
  next := fun A => Classical.choose (existsNext A)
  hom := fun A => Classical.choose (Classical.choose_spec (existsNext A))
  realizes := fun A => Classical.choose_spec (Classical.choose_spec (existsNext A))

namespace ofExists

/-- The successor refinement selected by `ofExists` realizes every request at its source target.
This is the stable specification of the chosen map, independent of its choice representation. -/
@[simp]
theorem realizes
    (existsNext :
      ∀ A : RefinementStage.{u, v, q, r, r'} S,
        ∃ B : RefinementStage.{u, v, q, r, r'} S,
          ∃ f : Hom A B, f.realizesAll (J := J))
    (A : RefinementStage.{u, v, q, r, r'} S) :
    ((ofExists (J := J) (S := S) existsNext).hom A).realizesAll (J := J) := sorry

end ofExists

/-- Recover the stagewise existence statement represented by an unseparated advance. -/
theorem toExists (advance : Advance.{u, v, q, r, r'} (J := J) (S := S)) :
    ∀ A : RefinementStage.{u, v, q, r, r'} S,
      ∃ B : RefinementStage.{u, v, q, r, r'} S,
        ∃ f : Hom A B, f.realizesAll (J := J) := sorry

end Advance
end RefinementStage
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
