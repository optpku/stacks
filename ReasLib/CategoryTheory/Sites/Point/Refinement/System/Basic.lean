/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Category.Preord
public import ReasLib.CategoryTheory.Sites.FiniteRefinement
public import ReasLib.CategoryTheory.Sites.Point.EssentiallySmallFiber.PresheafFiber

/-!
# Directed inverse systems

This module owns directed essentially-small inverse systems and the weaker
directed-preorder systems used before nonemptiness and smallness are available.
It also provides their fiber and point-construction APIs.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r r' r'' q w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/-- A nonempty directed inverse system with an essentially-small index in the chosen fiber
universe.  This bundles exactly the data needed to form its object fiber, raw presheaf fiber,
and eventually a point when cover-lifting data is supplied. -/
structure DirectedInverseSystem (C : Type u) [Category.{v} C] where
  /-- The preorder indexing the inverse system. -/
  index : Preord.{r}
  /-- The index is nonempty. -/
  nonempty : Nonempty index
  /-- The index is directed. -/
  directed : IsDirected index (· ≤ ·)
  /-- The inverse system. -/
  diagram : indexᵒᵖ ⥤ C
  /-- The index is essentially small in the fiber universe. -/
  fiberEssentiallySmall : EssentiallySmall.{q} indexᵒᵖ

namespace DirectedInverseSystem

variable {C : Type u} [Category.{v} C]

/-- Directed inverse systems are determined by their index preorder and inverse-system diagram;
nonemptiness, directedness, and essential smallness are proposition-valued. -/
@[ext]
theorem ext {S T : DirectedInverseSystem.{u, v, r, q} C}
    (h_index : S.index = T.index) (h_diagram : HEq S.diagram T.diagram) :
    S = T := sorry

/-- The index of a directed inverse system is nonempty. -/
instance indexNonempty (T : DirectedInverseSystem.{u, v, r, q} C) : Nonempty T.index :=
  T.nonempty

/-- The index of a directed inverse system is directed. -/
instance indexDirected (T : DirectedInverseSystem.{u, v, r, q} C) :
    IsDirected T.index (· ≤ ·) :=
  T.directed

/-- The index of a directed inverse system is essentially small in its fiber universe. -/
instance indexEssentiallySmall (T : DirectedInverseSystem.{u, v, r, q} C) :
    EssentiallySmall.{q} T.indexᵒᵖ :=
  T.fiberEssentiallySmall

/-- The object fiber of a directed inverse system. -/
noncomputable def fiber [LocallySmall.{q} C] (T : DirectedInverseSystem.{u, v, r, q} C) :
    C ⥤ Type q :=
  EssentiallySmallFiber.fiber T.diagram

/-- A canonical generator of the object fiber of a directed inverse system. -/
noncomputable def fiberMk [LocallySmall.{q} C] (T : DirectedInverseSystem.{u, v, r, q} C)
    {U : T.indexᵒᵖ} {W : C} (f : T.diagram.obj U ⟶ W) :
    T.fiber.obj W :=
  EssentiallySmallFiber.mk (S := T.diagram) f

/-- The raw presheaf fiber of a directed inverse system.  Its required colimit instances are
internal to the lower-level essentially-small cofiltered-fiber owner. -/
noncomputable def presheafFiber [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) :
    (Cᵒᵖ ⥤ Type q) ⥤ Type q :=
  EssentiallySmallFiber.Cofiltered.presheafFiber T.diagram

/-- The canonical germ map into the presheaf fiber of a directed inverse
system. This keeps the cofiltered-colimit implementation behind the bundled
system API. -/
noncomputable def toPresheafFiber [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) (X : C) (x : T.fiber.obj X)
    (F : Cᵒᵖ ⥤ Type q) :
    F.obj (op X) ⟶ T.presheafFiber.obj F :=
  EssentiallySmallFiber.Cofiltered.toPresheafFiber T.diagram X x F

/-- Canonical germs of a directed inverse system are natural in the
presheaf. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) {F G : Cᵒᵖ ⥤ Type q}
    (η : F ⟶ G) (X : C) (x : T.fiber.obj X) :
    T.toPresheafFiber X x F ≫ T.presheafFiber.map η =
      η.app (op X) ≫ T.toPresheafFiber X x G := sorry

/-- The category of elements of a directed inverse-system fiber is cofiltered. -/
theorem fiberIsCofiltered [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) :
    IsCofiltered T.fiber.Elements := sorry

/-- The category of elements of a directed inverse-system fiber is initially small in its fiber
universe. -/
theorem fiberInitiallySmall [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) :
    InitiallySmall.{q} T.fiber.Elements := sorry

/-- Construct a site point from a directed inverse system once its fiber lifts along all covering
sieves.  The underlying fiber functor remains exactly `T.fiber`. -/
noncomputable def toPoint [LocallySmall.{q} C]
    {J : GrothendieckTopology C} (T : DirectedInverseSystem.{u, v, r, q} C)
    (hT : GrothendieckTopology.Point.Fiber.coversLift J T.fiber) :
    GrothendieckTopology.Point.{q} J where
  fiber := T.fiber
  isCofiltered := T.fiberIsCofiltered
  initiallySmall := T.fiberInitiallySmall
  jointly_surjective := hT

/-- The point constructed from a directed inverse system has its canonical fiber functor. -/
@[simp]
theorem toPoint_fiber [LocallySmall.{q} C]
    {J : GrothendieckTopology C} (T : DirectedInverseSystem.{u, v, r, q} C)
    (hT : GrothendieckTopology.Point.Fiber.coversLift J T.fiber) :
    (T.toPoint hT).fiber = T.fiber := sorry

namespace FiniteCoverLifts

/-- Construct a point from a directed inverse system whose fiber lifts through finite covering
families, assuming the site has finite refinements.  The fiber and cover-index universes remain
independent, so this applies directly to refinement targets built in larger universes. -/
noncomputable def point [LocallySmall.{q} C]
    {J : GrothendieckTopology C} (T : DirectedInverseSystem.{u, v, r, q} C)
    (hJ : ∀ X : C, GrothendieckTopology.HasFiniteRefinement J X)
    (hT : Functor.FiniteCoverLifts.{u, v, q, w'} T.fiber J) :
    GrothendieckTopology.Point.{q} J :=
  T.toPoint (GrothendieckTopology.Point.Fiber.of_finite_cover_lifts hJ hT)

/-- The point constructed from finite-cover lifting has the original directed-system fiber. -/
@[simp]
theorem point_fiber [LocallySmall.{q} C]
    {J : GrothendieckTopology C} (T : DirectedInverseSystem.{u, v, r, q} C)
    (hJ : ∀ X : C, GrothendieckTopology.HasFiniteRefinement J X)
    (hT : Functor.FiniteCoverLifts.{u, v, q, w'} T.fiber J) :
    (point T hJ hT).fiber = T.fiber := sorry

end FiniteCoverLifts

end DirectedInverseSystem

/-- An inverse system indexed by a directed preorder, before nonemptiness and smallness are
recorded.  This is the appropriate owner for constructions that may obtain a nonempty index only
after producing a fiber element; `DirectedInverseSystem` is the refinement used once those
properties are available. -/
structure DirectedPreorderSystem (C : Type u) [Category.{v} C] where
  /-- The directed preorder indexing the inverse system. -/
  index : Preord.{r}
  /-- The index is directed. -/
  directed : IsDirected index (· ≤ ·)
  /-- The inverse-system diagram. -/
  diagram : indexᵒᵖ ⥤ C

namespace DirectedPreorderSystem

variable {C : Type u} [Category.{v} C]

/-- Directed preorder systems are determined by their index preorder and inverse-system diagram;
directedness is proposition-valued. -/
@[ext]
theorem ext {S T : DirectedPreorderSystem.{u, v, r} C}
    (h_index : S.index = T.index) (h_diagram : HEq S.diagram T.diagram) :
    S = T := sorry

/-- The directedness instance carried by a `DirectedPreorderSystem`. -/
instance indexDirected (D : DirectedPreorderSystem.{u, v, r} C) :
    IsDirected D.index (· ≤ ·) :=
  D.directed

/-- Add nonemptiness and essential smallness to obtain the canonical directed inverse-system
owner used by the fiber and point APIs. -/
noncomputable def toDirected
    (D : DirectedPreorderSystem.{u, v, r} C) (hD : Nonempty D.index)
    [EssentiallySmall.{q} D.indexᵒᵖ] :
    DirectedInverseSystem.{u, v, r, q} C where
  index := D.index
  nonempty := hD
  directed := D.directed
  diagram := D.diagram
  fiberEssentiallySmall := inferInstance

namespace toDirected

/-- Adding nonemptiness and smallness does not change the index preorder. -/
@[simp]
theorem index
    (D : DirectedPreorderSystem.{u, v, r} C) (hD : Nonempty D.index)
    [EssentiallySmall.{q} D.indexᵒᵖ] :
    (D.toDirected hD).index = D.index := sorry

/-- Adding nonemptiness and smallness does not change the inverse-system
diagram. -/
@[simp]
theorem diagram
    (D : DirectedPreorderSystem.{u, v, r} C) (hD : Nonempty D.index)
    [EssentiallySmall.{q} D.indexᵒᵖ] :
    (D.toDirected hD).diagram = D.diagram := sorry

end toDirected

end DirectedPreorderSystem

/- Data audit: the canonical germ is inherited from the neutral cofiltered
presheaf-fiber owner; its computational content introduces no proof debt. -/

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
