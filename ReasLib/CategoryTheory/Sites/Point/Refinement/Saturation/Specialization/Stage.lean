/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Category
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Separating

/-!
# Scheduled-Stage Specialization Bridges

This leaf forgets solved-request scheduling and separation data from `Stage`, first through the
separating-stage layer and then into the neutral `RefinementStage` API.
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

namespace Stage

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

/-- Forget the separating pair and solved-request set of a scheduled saturation stage. -/
noncomputable def toRefinementStage (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    RefinementStage.{u, v, q, r, r'} S :=
  A.toSeparatingStage.toRefinementStage

namespace toRefinementStage

/-- Forgetting scheduling and separation data retains the target stage. -/
@[simp]
theorem target (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.toRefinementStage.target = A.target := sorry

/-- The generic refinement of a forgotten scheduled stage is its original refinement. -/
@[simp]
theorem toRefinement (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.toRefinementStage.toRefinement = A.toRefinement := sorry

/-- Forgetting scheduling and separation does not change transport of a source request. -/
@[simp]
theorem mapRequest
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toRefinementStage.mapRequest request = A.mapRequest request := sorry

/-- Forgetting scheduling and separation does not change whether a source request is solved. -/
@[simp]
theorem solves_iff
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    A.toRefinementStage.solves request ↔ A.solves request := sorry

/-- Forgetting scheduling and separation preserves source completion. -/
@[simp]
theorem sourceComplete_iff
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    A.toRefinementStage.sourceComplete J ↔ A.sourceComplete := sorry

end toRefinementStage

namespace Hom

variable {A B : Stage.{u, v, q, r, r'} (J := J) S P x y}

/-- Forget the separation and solved-request packaging of a scheduled-stage morphism. -/
noncomputable def toRefinementStage (f : Hom A B) :
    RefinementStage.Hom A.toRefinementStage B.toRefinementStage :=
  f.toSeparatingStage.toRefinementStage

namespace toRefinementStage

/-- The generic refinement of a forgotten scheduled-stage morphism is unchanged. -/
@[simp]
theorem toRefinement (f : Hom A B) :
    f.toRefinementStage.toRefinement = f.toRefinement := sorry

/-- Forgetting scheduling and separation data does not change finite-cover request transport. -/
@[simp]
theorem mapRequest (f : Hom A B) (request : A.target.Request J) :
    f.toRefinementStage.mapRequest request = f.mapRequest request := sorry

/-- Forgetting scheduling and separation preserves the all-request realization predicate. -/
@[simp]
theorem realizesAll_iff (f : Hom A B) :
    f.toRefinementStage.realizesAll (J := J) ↔ f.realizesAll := sorry

end toRefinementStage

/-- Forgetting an identity scheduled-stage morphism gives the identity refinement-stage
morphism. -/
@[simp]
theorem id.toRefinementStage (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    (id A).toRefinementStage = RefinementStage.Hom.id A.toRefinementStage := sorry

/-- Forgetting a composite scheduled-stage morphism gives the composite refinement-stage
morphism. -/
@[simp]
theorem comp.toRefinementStage
    {A B D : Stage.{u, v, q, r, r'} (J := J) S P x y}
    (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinementStage =
      RefinementStage.Hom.comp f.toRefinementStage g.toRefinementStage := sorry

end Hom

/-- Forget solved-request scheduling while retaining the separating stage and its morphisms. -/
noncomputable def forgetSolved :
    Stage.{u, v, q, r, r'} (J := J) S P x y ⥤
      SeparatingStage.{u, v, q, r, r'} S P x y where
  obj := fun A => A.toSeparatingStage
  map := fun f => f.toSeparatingStage
  map_id := Hom.id.toSeparatingStage
  map_comp := Hom.comp.toSeparatingStage

namespace forgetSolved

/-- The scheduling-forgetful functor sends a stage to its underlying separating stage. -/
@[simp]
theorem obj (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    (forgetSolved (J := J) (S := S) (P := P) (x := x) (y := y)).obj A =
      A.toSeparatingStage := sorry

/-- The scheduling-forgetful functor sends a morphism to its underlying separating-stage
morphism. -/
@[simp]
theorem map {A B : Stage.{u, v, q, r, r'} (J := J) S P x y} (f : Hom A B) :
    (forgetSolved (J := J) (S := S) (P := P) (x := x) (y := y)).map f =
      f.toSeparatingStage := sorry

end forgetSolved

/-- Forget all saturation-specific predicates while retaining compatible refinements.  This
functor factors through the neutral separating-stage layer. -/
noncomputable def forget :
    Stage.{u, v, q, r, r'} (J := J) S P x y ⥤ RefinementStage.{u, v, q, r, r'} S :=
  forgetSolved (J := J) (S := S) (P := P) (x := x) (y := y) ⋙
    SeparatingStage.forget (S := S) (P := P) (x := x) (y := y)

namespace forget

/-- The saturation-forgetful functor sends a stage to its generic refinement stage. -/
@[simp]
theorem obj (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    (forget (J := J) (S := S) (P := P) (x := x) (y := y)).obj A =
      A.toRefinementStage := sorry

/-- The saturation-forgetful functor sends a morphism to its generic refinement-stage
morphism. -/
@[simp]
theorem map {A B : Stage.{u, v, q, r, r'} (J := J) S P x y} (f : Hom A B) :
    (forget (J := J) (S := S) (P := P) (x := x) (y := y)).map f =
      f.toRefinementStage := sorry

end forget
end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
