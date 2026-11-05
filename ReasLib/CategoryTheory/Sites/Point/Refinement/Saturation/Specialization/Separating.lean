/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.SeparatingStage.Category
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Category

/-!
# Separating-Stage Specialization Bridges

The unseparated `RefinementStage` layer does not import separation data. This leaf supplies the
explicit forgetful bridge from `SeparatingStage` to that neutral finite-cover API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace SeparatingStage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

namespace toRefinementStage

/-- Forgetting separation data retains the target stage. -/
@[simp]
theorem target (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    A.toRefinementStage.target = A.target := rfl

/-- The generic refinement of a forgotten separating stage is its original refinement. -/
@[simp]
theorem toRefinement (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    A.toRefinementStage.toRefinement = A.toRefinement := rfl

/-- Forgetting separation does not change transport of a request from the original system. -/
@[simp]
theorem mapRequest
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toRefinementStage.mapRequest request = A.mapRequest request := rfl

/-- Forgetting separation does not change whether a source request is solved. -/
@[simp]
theorem solves_iff
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toRefinementStage.solves request ↔ A.solves request := Iff.rfl

/-- Forgetting separation preserves source completion. -/
@[simp]
theorem sourceComplete_iff
    (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    A.toRefinementStage.sourceComplete J ↔ A.sourceComplete J := Iff.rfl

end toRefinementStage

namespace Hom

variable {A B : SeparatingStage.{u, v, q, r, r'} S P x y}

/-- Forget the separation-specific packaging of a separating-stage morphism. -/
noncomputable def toRefinementStage (f : Hom A B) :
    RefinementStage.Hom A.toRefinementStage B.toRefinementStage :=
  f.toBase

namespace toRefinementStage

/-- The generic refinement of a forgotten separating-stage morphism is unchanged. -/
@[simp]
theorem toRefinement (f : Hom A B) :
    f.toRefinementStage.toRefinement = f.toRefinement := rfl

/-- Forgetting separation data does not change finite-cover request transport. -/
@[simp]
theorem mapRequest (f : Hom A B) (request : A.target.Request J) :
    f.toRefinementStage.mapRequest request = f.mapRequest request := rfl

/-- Forgetting separation preserves the all-request realization predicate. -/
@[simp]
theorem realizesAll_iff (f : Hom A B) :
    f.toRefinementStage.realizesAll (J := J) ↔ f.realizesAll (J := J) := Iff.rfl

end toRefinementStage

/-- Forgetting an identity separating-stage morphism gives the identity refinement-stage
morphism. -/
@[simp]
theorem id.toRefinementStage (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    (id A).toRefinementStage = RefinementStage.Hom.id A.toRefinementStage := rfl

/-- Forgetting a composite separating-stage morphism gives the composite refinement-stage
morphism. -/
@[simp]
theorem comp.toRefinementStage
    {A B D : SeparatingStage.{u, v, q, r, r'} S P x y}
    (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinementStage =
      RefinementStage.Hom.comp f.toRefinementStage g.toRefinementStage := rfl

end Hom

/-- The functor forgetting only separation data from separating refinement stages. -/
noncomputable def forget :
    SeparatingStage.{u, v, q, r, r'} S P x y ⥤ RefinementStage.{u, v, q, r, r'} S where
  obj := fun A => A.toRefinementStage
  map := fun f => f.toRefinementStage
  map_id := Hom.id.toRefinementStage
  map_comp := Hom.comp.toRefinementStage

namespace forget

/-- The separation-forgetful functor sends a stage to its generic refinement stage. -/
@[simp]
theorem obj (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    (forget (S := S) (P := P) (x := x) (y := y)).obj A = A.toRefinementStage := rfl

/-- The separation-forgetful functor sends a morphism to its generic refinement-stage
morphism. -/
@[simp]
theorem map {A B : SeparatingStage.{u, v, q, r, r'} S P x y} (f : Hom A B) :
    (forget (S := S) (P := P) (x := x) (y := y)).map f = f.toRefinementStage := rfl

end forget
end SeparatingStage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
