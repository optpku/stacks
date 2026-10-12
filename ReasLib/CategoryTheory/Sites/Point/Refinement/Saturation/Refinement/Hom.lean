/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Category

/-!
# Morphisms of finite-cover refinement stages

This leaf owns compatible refinements between finite-cover refinement stages,
their request-transport API, and the bridge to source-free target morphisms.
Identity, composition, and category structure are layered separately.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' r'' w'

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

/-- A morphism of finite-cover refinement stages is a further refinement compatible with their
refinements from the original system. -/
structure Hom
    (A : RefinementStage.{u, v, q, r, r'} S)
    (B : RefinementStage.{u, v, q, r, r''} S) where
  /-- The ordered refinement between the two target systems. -/
  refinement : OrderedRefinement A.diagram B.diagram
  /-- The target refinement factors through the source refinement. -/
  factorization : IsFactorization A.toRefinement refinement B.toRefinement

namespace Hom

variable {A : RefinementStage.{u, v, q, r, r'} S}
variable {B : RefinementStage.{u, v, q, r, r''} S}

/-- The ordered refinement carried by a refinement-stage morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  f.refinement

/-- Transport a finite-cover request along a refinement-stage morphism. -/
noncomputable def mapRequest (f : Hom A B) (request : A.target.Request J) :
    B.target.Request J :=
  f.toRefinement.mapRequest request

namespace mapRequest

/-- A realized target request remains realized after transport along a compatible
refinement-stage morphism. -/
theorem isRealized (f : Hom A B) (request : A.target.Request J) :
    request.is_realized → (f.mapRequest request).is_realized := sorry

/-- Transport through a compatible stage morphism agrees with direct transport from the
original system. -/
theorem fromSource (f : Hom A B)
    (request : EssentiallySmallFiber.CoverLift.Request J S) :
    f.mapRequest (A.mapRequest request) = B.mapRequest request := sorry

end mapRequest

/-- A refinement-stage morphism realizes every finite-cover request already present at its
source target. -/
def realizesAll (f : Hom A B) : Prop :=
  ∀ request : A.target.Request J, (f.mapRequest request).is_realized

/-- Realizing every source-target request is finite-cover lifting by the underlying refinement. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll (J := J) ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J := sorry

/-- Forget the common-source factorization condition from a refinement-stage morphism, retaining
the underlying source-free target refinement. -/
noncomputable def toTarget (f : Hom A B) : Target.Hom A.target B.target where
  refinement := f.toRefinement

namespace toTarget

/-- The target refinement underlying a forgotten refinement-stage morphism is unchanged. -/
@[simp]
theorem toRefinement (f : Hom A B) :
    f.toTarget.toRefinement = f.toRefinement := sorry

/-- Forgetting the common-source factorization does not change finite-cover request transport. -/
@[simp]
theorem mapRequest (f : Hom A B) (request : A.target.Request J) :
    f.toTarget.mapRequest request = f.mapRequest request := sorry

/-- Forgetting the common-source factorization preserves the all-request realization
predicate. -/
@[simp]
theorem realizesAll_iff (f : Hom A B) :
    f.toTarget.realizesAll (J := J) ↔ f.realizesAll (J := J) := sorry

end toTarget
end Hom
end RefinementStage

end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
