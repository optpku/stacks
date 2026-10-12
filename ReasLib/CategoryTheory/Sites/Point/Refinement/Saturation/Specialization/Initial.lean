/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Base
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Stage

/-!
# Initial separating and scheduled stages

This leaf lifts the neutral initial `RefinementStage` through the separation
and solved-request layers.  Each constructor adds only the semantic field owned
by its layer.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

namespace SeparatingStage

/-- Add a chosen separation witness to a neutral refinement stage. -/
noncomputable def ofRefinementStage
    (A : RefinementStage.{u, v, q, r, r'} S)
    (separates : OrderedRefinement.EssentiallySmall.Separates A.toRefinement P x y) :
    SeparatingStage.{u, v, q, r, r'} S P x y where
  target := A.target
  refinement := A.toRefinement
  separates := separates

namespace ofRefinementStage

/-- Forgetting separation from `ofRefinementStage` recovers the neutral stage. -/
@[simp]
theorem toRefinementStage
    (A : RefinementStage.{u, v, q, r, r'} S)
    (separates : OrderedRefinement.EssentiallySmall.Separates A.toRefinement P x y) :
    (ofRefinementStage A separates).toRefinementStage = A := sorry

/-- The target of `ofRefinementStage` is the target of its neutral input. -/
@[simp]
theorem target
    (A : RefinementStage.{u, v, q, r, r'} S)
    (separates : OrderedRefinement.EssentiallySmall.Separates A.toRefinement P x y) :
    (ofRefinementStage A separates).target = A.target := sorry

/-- The refinement of `ofRefinementStage` is the refinement of its neutral input. -/
@[simp]
theorem toRefinement
    (A : RefinementStage.{u, v, q, r, r'} S)
    (separates : OrderedRefinement.EssentiallySmall.Separates A.toRefinement P x y) :
    (ofRefinementStage A separates).toRefinement = A.toRefinement := sorry

end ofRefinementStage

/-- The canonical initial separating stage on a directed preorder diagram. -/
noncomputable def base (hxy : x ≠ y) :
    SeparatingStage.{u, v, q, r, r} S P x y :=
  ofRefinementStage (RefinementStage.base S)
    (RefinementStage.base.separates S P hxy)

namespace base

/-- Forgetting separation from the initial separating stage gives the neutral
initial refinement stage. -/
@[simp]
theorem toRefinementStage (hxy : x ≠ y) :
    (base hxy).toRefinementStage = RefinementStage.base S := sorry

/-- The initial separating stage carries the identity refinement. -/
@[simp]
theorem toRefinement (hxy : x ≠ y) :
    (base hxy).toRefinement = OrderedRefinement.id S := sorry

end base

end SeparatingStage

namespace Stage

/-- Add a solved-request set and its realization certificate to a separating stage. -/
noncomputable def ofSeparatingStage
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (solved : Set (A.target.Request J))
    (solvedRealized : ∀ ⦃request : A.target.Request J⦄,
      request ∈ solved → request.is_realized) :
  Stage.{u, v, q, r, r'} (J := J) S P x y where
  toSeparatingStage := A
  solved := solved
  solvedRealized := solvedRealized

namespace ofSeparatingStage

/-- Forgetting scheduling from `ofSeparatingStage` recovers the separating stage. -/
@[simp]
theorem toSeparatingStage
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (solved : Set (A.target.Request J))
    (solvedRealized : ∀ ⦃request : A.target.Request J⦄,
      request ∈ solved → request.is_realized) :
    (ofSeparatingStage A solved solvedRealized).toSeparatingStage = A := sorry

/-- The solved set of `ofSeparatingStage` is the supplied solved set. -/
@[simp]
theorem solved
    (A : SeparatingStage.{u, v, q, r, r'} S P x y)
    (solved : Set (A.target.Request J))
    (solvedRealized : ∀ ⦃request : A.target.Request J⦄,
      request ∈ solved → request.is_realized) :
    (ofSeparatingStage A solved solvedRealized).solved = solved := sorry

end ofSeparatingStage

/-- The empty solved-request set satisfies the realization invariant at every
separating stage. -/
theorem emptySolvedRealized (A : SeparatingStage.{u, v, q, r, r'} S P x y) :
    ∀ ⦃request : A.target.Request J⦄,
      request ∈ (∅ : Set (A.target.Request J)) → request.is_realized := sorry

/-- The canonical initial scheduled stage has the original target, preserves
the chosen separation, and records no solved requests. -/
noncomputable def base (hxy : x ≠ y) :
    Stage.{u, v, q, r, r} (J := J) S P x y :=
  ofSeparatingStage (SeparatingStage.base hxy) ∅
    (emptySolvedRealized (J := J) (SeparatingStage.base hxy))

namespace base

/-- Forgetting scheduling from the initial scheduled stage gives the initial
separating stage. -/
@[simp]
theorem toSeparatingStage (hxy : x ≠ y) :
    (base (J := J) hxy).toSeparatingStage = SeparatingStage.base hxy := sorry

/-- Forgetting all specialized data from the initial scheduled stage gives the
neutral initial refinement stage. -/
@[simp]
theorem toRefinementStage (hxy : x ≠ y) :
    (base (J := J) hxy).toRefinementStage = RefinementStage.base S := sorry

/-- The initial scheduled stage records no solved requests. -/
@[simp]
theorem solved (hxy : x ≠ y) :
    (base (J := J) hxy).solved = ∅ := sorry

/-- The initial scheduled stage carries the identity refinement. -/
@[simp]
theorem toRefinement (hxy : x ≠ y) :
    (base (J := J) hxy).toRefinement = OrderedRefinement.id S := sorry

end base

end Stage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
