/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Step.Basic

/-!
# Computations for one-request saturation steps

This leaf exposes the composite base map, local request transport, and the
explicit constructor projections needed by recursive applications.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.Step

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
variable {base : A ⟶ L} {request : A.target.Request J}

/-- One-request steps with the same next stage and transition are equal. -/
@[ext]
theorem ext {step₁ step₂ : Step base request}
    (hstage : step₁.stage = step₂.stage) (hhom : HEq step₁.hom step₂.hom) :
    step₁ = step₂ := sorry

namespace fromBase

/-- The base map of a one-request step is the prescribed base map followed by
the stored transition. -/
@[simp]
theorem eq (step : Step base request) :
    step.fromBase = base ≫ step.hom := sorry

/-- Transport along a step's composite base map is transport to the current
stage followed by transport along the stored transition. -/
@[simp]
theorem mapRequest (step : Step base request) :
    step.fromBase.mapRequest request =
      step.hom.mapRequest (base.mapRequest request) := sorry

end fromBase

/-- The request transported to the current stage is realized after the
stored transition of a one-request step. -/
theorem realizesLocal (step : Step base request) :
    (step.hom.mapRequest (base.mapRequest request)).is_realized := sorry

namespace ofLocal

/-- `ofLocal` retains its explicitly supplied next stage. -/
@[simp]
theorem stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).stage = B := sorry

/-- `ofLocal` retains its explicitly supplied transition. -/
@[simp]
theorem hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).hom = f := sorry

/-- The base map of `ofLocal` is the explicit composite of its inputs. -/
@[simp]
theorem fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).fromBase = base ≫ f := sorry

end ofLocal

namespace ofExists

/-- The transition selected by `ofExists` realizes the prescribed request
after the fixed base map. -/
@[simp]
theorem realizes
    (h : ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized) :
    ((base ≫ (ofExists h).hom).mapRequest request).is_realized := sorry

/-- The transition selected by `ofExists` realizes the request transported to
the current stage. -/
@[simp]
theorem realizesLocal
    (h : ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized) :
    ((ofExists h).hom.mapRequest (base.mapRequest request)).is_realized := sorry

end ofExists

end Stage.Scheduled.Step
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
