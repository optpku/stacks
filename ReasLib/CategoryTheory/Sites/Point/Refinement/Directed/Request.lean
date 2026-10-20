/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.Hom
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Request

/-!
# Finite-cover requests along directed refinements

This file owns request transport and solution predicates for fixed-endpoint
refinement morphisms and directed refinements.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r r' r'' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedInverseSystem

variable {C : Type u} [Category.{v} C]
variable {X : DirectedInverseSystem.{u, v, r, q} C}
variable {Y : DirectedInverseSystem.{u, v, r', q} C}
variable {Z : DirectedInverseSystem.{u, v, r'', q} C}
variable {J : GrothendieckTopology C}

namespace RefinementHom

/-- Transport an essentially-small finite-cover request along a fixed-endpoint refinement. -/
noncomputable def mapRequest [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    EssentiallySmallFiber.CoverLift.Request J Y.diagram :=
  f.toOrdered.mapRequest request

/-- Forgetting endpoints gives the same request transport as the
fixed-endpoint interface. -/
@[simp]
theorem toOrdered.mapRequest [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    f.toOrdered.mapRequest request = f.mapRequest request := sorry

/-- A request realized at the source remains realized after fixed-endpoint transport. -/
theorem mapRequest.isRealized [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    request.is_realized → (f.mapRequest request).is_realized := sorry

/-- Transport along the identity fixed-endpoint refinement is the identity on requests. -/
@[simp]
theorem id.mapRequest [LocallySmall.{q} C]
    (X : DirectedInverseSystem.{u, v, r, q} C)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    (id X).mapRequest request = request := sorry

/-- Request transport respects composition of fixed-endpoint refinements. -/
@[simp]
theorem comp.mapRequest [LocallySmall.{q} C]
    (f : RefinementHom X Y) (g : RefinementHom Y Z)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    (f.comp g).mapRequest request = g.mapRequest (f.mapRequest request) := sorry

/-- A fixed-endpoint refinement solves a request when its transported request is realized. -/
def solves [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) : Prop :=
  request.is_solved_by f.fiberMap

/-- A fixed-endpoint refinement solves a request exactly when its transport is realized. -/
@[simp]
theorem solves_iff [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    f.solves request ↔ (f.mapRequest request).is_realized := sorry

/-- Forgetting endpoints preserves the request-solving predicate. -/
@[simp]
theorem toOrdered.solves_iff [LocallySmall.{q} C] (f : RefinementHom X Y)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    f.toOrdered.solves request ↔ f.solves request := sorry

/-- The identity fixed-endpoint refinement solves exactly the already-realized
requests. -/
@[simp]
theorem id.solves_iff [LocallySmall.{q} C]
    (X : DirectedInverseSystem.{u, v, r, q} C)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    (id X).solves request ↔ request.is_realized := sorry

/-- A request solved by a fixed-endpoint refinement remains solved after composition. -/
theorem comp.solves [LocallySmall.{q} C] (f : RefinementHom X Y)
    (g : RefinementHom Y Z)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    f.solves request → (f.comp g).solves request := sorry

/-- A composite fixed-endpoint refinement solves a request exactly when its
second factor solves the transported request. -/
@[simp]
theorem comp.solves_iff [LocallySmall.{q} C] (f : RefinementHom X Y)
    (g : RefinementHom Y Z)
    (request : EssentiallySmallFiber.CoverLift.Request J X.diagram) :
    (f.comp g).solves request ↔ g.solves (f.mapRequest request) := sorry

end RefinementHom

end DirectedInverseSystem

namespace DirectedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι] {S : ιᵒᵖ ⥤ C}
variable {J : GrothendieckTopology C}

/-- A finite-cover request attached to the source fiber owned by a directed refinement. -/
noncomputable abbrev Request [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (J : GrothendieckTopology C) :=
  Functor.CoverLift.Request J R.sourceFiber

/-- Transport a source-fiber request along a directed refinement. -/
noncomputable def mapRequest [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) :
    Functor.CoverLift.Request J R.target.fiber :=
  request.map R.fiberMap

/-- The fixed-endpoint bridge transports source requests exactly as the
bundled directed refinement does. -/
@[simp]
theorem toRefinementHom.mapRequest [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) :
    R.toRefinementHom.mapRequest request = R.mapRequest request := sorry

/-- A request realized before a directed refinement remains realized after transport. -/
theorem mapRequest.isRealized [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) :
    request.is_realized → (R.mapRequest request).is_realized := sorry

/-- Transport along the identity directed refinement is the identity on requests. -/
@[simp]
theorem id.mapRequest [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) (request : Request (id T) J) :
    (id T).mapRequest request = request := sorry

/-- Request transport along a composite directed refinement is successive transport. -/
@[simp]
theorem comp.mapRequest [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram)
    (request : Request R J) :
    (R.comp Q).mapRequest request = Q.mapRequest (R.mapRequest request) := sorry

/-- A directed refinement solves a source-fiber request when its fiber map solves it. -/
def solves [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) : Prop :=
  request.is_solved_by R.fiberMap

/-- A directed refinement solves a request exactly when its transport is realized. -/
@[simp]
theorem solves_iff [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) :
    R.solves request ↔ (R.mapRequest request).is_realized := sorry

/-- The fixed-endpoint bridge preserves the request-solving predicate. -/
@[simp]
theorem toRefinementHom.solves_iff [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (request : Request R J) :
    R.toRefinementHom.solves request ↔ R.solves request := sorry

/-- The identity directed refinement solves exactly the already-realized
requests. -/
@[simp]
theorem id.solves_iff [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C)
    (request : Request (id T) J) :
    (id T).solves request ↔ request.is_realized := sorry

/-- A request solved by a directed refinement remains solved after composition. -/
theorem comp.solves [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram)
    (request : Request R J) :
    R.solves request → (R.comp Q).solves request := sorry

/-- A composite directed refinement solves a request exactly when its second
factor solves the transported request. -/
@[simp]
theorem comp.solves_iff [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram)
    (request : Request R J) :
    (R.comp Q).solves request ↔ Q.solves (R.mapRequest request) := sorry

end DirectedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
