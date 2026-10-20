/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Category

/-!
# One-request saturation steps

This leaf owns the neutral datum for extending a current saturation stage
while realizing one request transported from a fixed base stage.  It does not
choose an enumeration, an ordinal recursion, or a construction of the next
stage.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {A L : Stage.{u, v, q, r, r'} (J := J) S P x y}

/-- A one-request saturation step after a compatible map `base : A ⟶ L`.
The stored morphism starts at the current stage `L`; realization is stated
after composing it with the fixed base map. -/
structure Step (base : A ⟶ L) (request : A.target.Request J) where
  /-- The stage obtained after the one-request extension. -/
  stage : Stage.{u, v, q, r, r'} (J := J) S P x y
  /-- The compatible refinement from the current stage to the new stage. -/
  hom : L ⟶ stage
  /-- The prescribed base request is realized after the composite refinement. -/
  realizes : ((base ≫ hom).mapRequest request).is_realized

namespace Step

variable {base : A ⟶ L} {request : A.target.Request J}

/-- The composite compatible refinement from the fixed base stage to the
stage of a one-request step. -/
noncomputable def fromBase (step : Step base request) : A ⟶ step.stage :=
  base ≫ step.hom

/-- Local realization data at the current stage implies the composite
realization law required by a one-request step. -/
theorem ofLocalRealizes
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    ((base ≫ f).mapRequest request).is_realized := sorry

/-- Construct a one-request step from an explicit next stage, transition,
and realization of the request already transported to the current stage. -/
noncomputable def ofLocal
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    Step base request where
  stage := B
  hom := f
  realizes := ofLocalRealizes B f hreal

/-- A one-request step supplies an explicit extension stage and transition
realizing the prescribed request after the fixed base map. -/
theorem toExists (step : Step base request) :
    ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized := sorry

/-- Choose a one-request step from an explicit existence proof of an extension
stage and a compatible transition realizing the request. -/
noncomputable def ofExists
    (h : ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized) :
    Step base request where
  stage := h.choose
  hom := h.choose_spec.choose
  realizes := h.choose_spec.choose_spec

/- The stage and transition selected by `Step.ofLocal` and `Step.ofExists` are
explicit.  Their audit can inherit `sorryAx` from the proposition-valued
realization fields and the existing `Stage` category laws; the selected
non-Prop fields themselves use only the supplied data or `Classical.choice`. -/

end Step
end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
