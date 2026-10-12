/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCheckRecall

@[expose]
public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The stalk construction only needs an initial-smallness witness; cofilteredness
is not part of the source definition. -/
noncomputable def topologyStalk (J : GrothendieckTopology C)
    (u : C ⥤ Type w) (h : InitiallySmall.{w} u.Elements) :
    Sheaf J (Type w) ⥤ Type w :=
  -- Local instance justification (proof-local temporary data): the explicit
  -- size witness supplies the standard colimit API for the stalk construction.
  letI := h
  letI : HasColimitsOfShape u.Elementsᵒᵖ (Type w) :=
    hasColimitsOfShape_of_finallySmall _ _
  sheafToPresheaf J (Type w) ⋙
    (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π u).op ⋙ colim

/-- Definition 7.52.1: Let `C` be a category and `J` a Grothendieck topology on
`C`. A point of the topology is given by a functor `u : C ⥤ Type w` such that
covering sieves are stalk-surjective and the stalk functor on sheaves is exact.
-/
@[stacks 00ZT]
structure CategoryTheory.GrothendieckTopology.PointOfTopology
    (J : GrothendieckTopology C) where
  fiber : C ⥤ Type w
  initiallySmall : InitiallySmall.{w} fiber.Elements
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x
  stalk_exact : exactFunctor (Sheaf J (Type w)) (Type w)
    (topologyStalk J fiber initiallySmall)

namespace CategoryTheory.GrothendieckTopology.PointOfTopology

noncomputable def sheafFiber
    (J : GrothendieckTopology C)
    (p : PointOfTopology J) :
    Sheaf J (Type w) ⥤ Type w :=
  topologyStalk J p.fiber p.initiallySmall

/-- The stalk functor of a source-faithful point is the colimit stalk
construction associated to its fiber functor. -/
theorem sheafFiber_eq
    (J : GrothendieckTopology C)
    (p : PointOfTopology J) :
    p.sheafFiber = topologyStalk J p.fiber p.initiallySmall := sorry

end CategoryTheory.GrothendieckTopology.PointOfTopology
