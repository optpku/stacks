/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    step₁ = step₂ := by
  cases step₁ with
  | mk stage₁ hom₁ realizes₁ =>
    cases step₂ with
    | mk stage₂ hom₂ realizes₂ =>
      cases hstage
      cases hhom
      rfl

namespace fromBase

/-- The base map of a one-request step is the prescribed base map followed by
the stored transition. -/
@[simp]
theorem eq (step : Step base request) :
    step.fromBase = base ≫ step.hom := rfl

/-- Transport along a step's composite base map is transport to the current
stage followed by transport along the stored transition. -/
@[simp]
theorem mapRequest (step : Step base request) :
    step.fromBase.mapRequest request =
      step.hom.mapRequest (base.mapRequest request) := by
  change Stage.Hom.mapRequest (Stage.Hom.comp base step.hom) request =
    Stage.Hom.mapRequest step.hom (Stage.Hom.mapRequest base request)
  exact Stage.Hom.comp.mapRequest base step.hom request

end fromBase

/-- The request transported to the current stage is realized after the
stored transition of a one-request step. -/
theorem realizesLocal (step : Step base request) :
    (step.hom.mapRequest (base.mapRequest request)).is_realized := by
  rw [← fromBase.mapRequest step]
  exact step.realizes

namespace ofLocal

/-- `ofLocal` retains its explicitly supplied next stage. -/
@[simp]
theorem stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).stage = B := rfl

/-- `ofLocal` retains its explicitly supplied transition. -/
@[simp]
theorem hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).hom = f := rfl

/-- The base map of `ofLocal` is the explicit composite of its inputs. -/
@[simp]
theorem fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : L ⟶ B)
    (hreal : (f.mapRequest (base.mapRequest request)).is_realized) :
    (ofLocal B f hreal).fromBase = base ≫ f := rfl

end ofLocal

namespace ofExists

/-- The transition selected by `ofExists` realizes the prescribed request
after the fixed base map. -/
@[simp]
theorem realizes
    (h : ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized) :
    ((base ≫ (ofExists h).hom).mapRequest request).is_realized := by
  exact (ofExists h).realizes

/-- The transition selected by `ofExists` realizes the request transported to
the current stage. -/
@[simp]
theorem realizesLocal
    (h : ∃ (B : Stage.{u, v, q, r, r'} (J := J) S P x y), ∃ f : L ⟶ B,
      ((base ≫ f).mapRequest request).is_realized) :
    ((ofExists h).hom.mapRequest (base.mapRequest request)).is_realized := by
  rw [← fromBase.mapRequest (ofExists h)]
  exact (ofExists h).realizes

end ofExists

end Stage.Scheduled.Step
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
