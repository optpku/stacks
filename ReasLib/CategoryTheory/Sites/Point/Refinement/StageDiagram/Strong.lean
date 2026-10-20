/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.Request

/-!
# Strong refinement-stage diagrams

This file adds the nonemptiness and essential-smallness data needed by fiber and point
constructions, together with strong cocones and the forgetful bridges to the lower layer.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r r' q

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedInverseSystem

/-- A strong wrapper around a lower stage diagram.  It adds exactly the nonemptiness and
smallness data needed by fiber and point constructions, while leaving the lower diagram as the
single direct-limit owner. -/
structure StageDiagram (δ : Type d) [Preorder δ]
    (C : Type u) [Category.{v} C] where
  /-- The lower direct-union diagram. -/
  lower : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C
  /-- Each stage index is nonempty. -/
  nonempty : ∀ a : δ, Nonempty (lower.obj a).index
  /-- Each stage index is essentially small in the chosen fiber universe. -/
  fiberEssentiallySmall : ∀ a : δ, EssentiallySmall.{q} (lower.obj a).indexᵒᵖ

namespace StageDiagram

variable {δ : Type d} [Preorder δ]
variable (D : StageDiagram.{u, v, d, r, q} δ C)

/-- Strong stage diagrams are determined by their lower diagram; the added
nonemptiness and essential-smallness fields are proposition-valued. -/
@[ext]
theorem ext {D E : StageDiagram.{u, v, d, r, q} δ C}
    (h_lower : D.lower = E.lower) : D = E := sorry

/-- The directed inverse system at one stage of a strong diagram. -/
noncomputable def obj (a : δ) : DirectedInverseSystem.{u, v, r, q} C where
  index := (D.lower.obj a).index
  nonempty := D.nonempty a
  directed := (D.lower.obj a).directed
  diagram := (D.lower.obj a).diagram
  fiberEssentiallySmall := D.fiberEssentiallySmall a

/-- The refinement morphism induced by one lower diagram comparison. -/
noncomputable def map {a b : δ} (hab : a ≤ b) :
    RefinementHom (D.obj a) (D.obj b) where
  embedding := (D.lower.map hab).embedding
  restrictionIso := (D.lower.map hab).restrictionIso

namespace map

/-- A reflexive strong-diagram comparison is the identity refinement. -/
theorem refl (a : δ) :
    D.map (a := a) (b := a) le_rfl = RefinementHom.id (D.obj a) := sorry

/-- Strong-diagram refinements compose along comparable stages. -/
theorem comp {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c) :
    D.map (le_trans hab hbc) = (D.map hab).comp (D.map hbc) := sorry

/-- A composed stage transition has the expected composite order embedding. -/
theorem compEmbedding {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c) :
    (D.map (le_trans hab hbc)).embedding =
      (D.map hab).embedding.comp (D.map hbc).embedding := sorry

end map

/-- A compatible cocone of refinement morphisms out of a stage diagram.  Its vertex index may
live in a universe different from the component indices. -/
structure Cocone (D : StageDiagram.{u, v, d, r, q} δ C) where
  /-- The directed inverse system receiving all stage refinements. -/
  vertex : DirectedInverseSystem.{u, v, r', q} C
  /-- The refinement morphism from each stage into the cocone vertex. -/
  leg : ∀ a : δ, RefinementHom (D.obj a) vertex
  /-- Each leg agrees with the composite along every stage transition. -/
  leg_comp : ∀ {a b : δ} (hab : a ≤ b),
    (D.map hab).comp (leg b) = leg a

/-- The lower direct-union diagram is the canonical owner for the strong wrapper. -/
abbrev toPreorder :
    DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C :=
  D.lower

end StageDiagram

namespace StageDiagram.Cocone

variable {δ : Type d} [Preorder δ]
variable {D : DirectedInverseSystem.StageDiagram.{u, v, d, r, q} δ C}
variable {J : GrothendieckTopology C}

/-- Strong refinement cocones are determined by their vertex and legs; the
compatibility law is proposition-valued. -/
@[ext]
theorem ext {Q R : DirectedInverseSystem.StageDiagram.Cocone D}
    (h_vertex : Q.vertex = R.vertex) (h_leg : HEq Q.leg R.leg) :
    Q = R := sorry

section Requests

variable [LocallySmall.{q} C]

/-- Transport an essentially-small finite-cover request from one stage through a strong cocone.
The cocone leg is the only data needed by downstream request-scheduling code. -/
noncomputable def mapRequest
    (Q : DirectedInverseSystem.StageDiagram.Cocone D) (a : δ)
    (r : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram) :
    EssentiallySmallFiber.CoverLift.Request J Q.vertex.diagram :=
  (Q.leg a).mapRequest r

namespace mapRequest

/-- Request transport through strong cocone legs is natural in the stage
index. -/
@[simp] theorem naturality
    (Q : DirectedInverseSystem.StageDiagram.Cocone D)
    {a b : δ} (hab : a ≤ b)
    (r : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram) :
    Q.mapRequest a r = Q.mapRequest b ((D.map hab).mapRequest r) := sorry

/-- Realization of a request is preserved by every strong cocone leg. -/
theorem isRealized
    (Q : DirectedInverseSystem.StageDiagram.Cocone D) (a : δ)
    (r : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram) :
    r.is_realized → (Q.mapRequest a r).is_realized := sorry

end mapRequest

/-- A stage request is solved by a strong cocone when its cocone transport is realized. -/
def isSolvedBy
    (Q : DirectedInverseSystem.StageDiagram.Cocone D) (a : δ)
    (r : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram) : Prop :=
  (Q.leg a).solves r

/-- The cocone-level solved predicate is exactly realization after request transport. -/
@[simp] theorem isSolvedBy_iff
    (Q : DirectedInverseSystem.StageDiagram.Cocone D) (a : δ)
    (r : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram) :
    Q.isSolvedBy a r ↔ (Q.mapRequest a r).is_realized := sorry

end Requests

namespace toPreorder

/-- The lower cocone vertex obtained by forgetting strong fields. -/
noncomputable def vertex (Q : DirectedInverseSystem.StageDiagram.Cocone D) :
    DirectedPreorderSystem.{u, v, r'} C where
  index := Q.vertex.index
  directed := Q.vertex.directed
  diagram := Q.vertex.diagram

/-- One lower cocone leg obtained by forgetting strong fields. -/
noncomputable def leg
    (Q : DirectedInverseSystem.StageDiagram.Cocone D) (a : δ) :
    OrderedRefinement (D.toPreorder.obj a).diagram (vertex Q).diagram where
  embedding := (Q.leg a).embedding
  restrictionIso := (Q.leg a).restrictionIso

/-- Coherence of the lower cocone obtained from a strong cocone. -/
theorem legComp (Q : DirectedInverseSystem.StageDiagram.Cocone D)
    {a b : δ} (hab : a ≤ b) :
    (D.toPreorder.map hab).comp (leg Q b) = leg Q a := sorry

end toPreorder

/-- Forget the nonemptiness and smallness fields from a strong cocone. -/
noncomputable def toPreorder (Q : DirectedInverseSystem.StageDiagram.Cocone D) :
    DirectedPreorderSystem.StageDiagram.Cocone D.toPreorder where
  vertex := toPreorder.vertex Q
  leg := toPreorder.leg Q
  leg_comp := toPreorder.legComp Q

end StageDiagram.Cocone

end DirectedInverseSystem

namespace DirectedPreorderSystem.StageDiagram

variable {δ : Type d} [Preorder δ]
variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)

/-- Upgrade a lower stage diagram when every stage has the nonemptiness and smallness data needed
by fiber and point constructions.  The direct-union layer itself does not require these inputs. -/
noncomputable def toDirected
    (h_nonempty : ∀ a : δ, Nonempty (D.obj a).index)
    [∀ a : δ, EssentiallySmall.{q} (D.obj a).indexᵒᵖ] :
    DirectedInverseSystem.StageDiagram.{u, v, d, r, q} δ C where
  lower := D
  nonempty := h_nonempty
  fiberEssentiallySmall := fun _ => inferInstance

end DirectedPreorderSystem.StageDiagram

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
