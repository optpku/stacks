module

public import ReasLib.CategoryTheory.Sites.Point.Definition
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The stalk on sheaves associated to a set-valued functor with an explicit
initial-smallness witness for its category of elements. -/
noncomputable def topologyStalk (J : GrothendieckTopology C)
    (fiber : C ⥤ Type w) (h : InitiallySmall.{w} fiber.Elements) :
    Sheaf J (Type w) ⥤ Type w :=
  -- Local instance justification (proof-local temporary data): Register the supplied InitiallySmall proof only within this adapter because siteStalk's colimit API requires class arguments.
  letI := h
  -- Local instance justification (proof-local temporary data): Derive the canonical colimit-existence proof from the supplied smallness proof solely to apply siteStalk; no point or fiber data is selected.
  letI : HasColimitsOfShape fiber.Elementsᵒᵖ (Type w) :=
    hasColimitsOfShape_of_finallySmall _ _
  siteStalk J fiber

/-- A point of a Grothendieck topology consists of a set-valued fiber functor
whose category of elements is initially small, whose elements lift along
covering sieves, and whose stalk functor on sheaves preserves finite limits
and finite colimits. -/
structure PointOfTopology (J : GrothendieckTopology C) where
  /-- The set-valued fiber functor on the underlying category. -/
  fiber : C ⥤ Type w
  /-- The size condition for forming stalks in the fiber's set universe. -/
  initiallySmall : InitiallySmall.{w} fiber.Elements
  /-- Every fiber element lifts along an arrow of any covering sieve. -/
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x
  /-- The canonical stalk functor on sheaves is exact. -/
  stalk_exact : exactFunctor (Sheaf J (Type w)) (Type w)
    (topologyStalk J fiber initiallySmall)

namespace PointOfTopology

variable {J : GrothendieckTopology C}

/-- Construct a topology point from a supplied fiber functor, its size witness,
covering-surjectivity proof, and exactness proof for its canonical stalk. -/
def of (fiber : C ⥤ Type w) (initiallySmall : InitiallySmall.{w} fiber.Elements)
    (jointly_surjective : ∀ {X : C} (R : Sieve X), R ∈ J X → ∀ x : fiber.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x)
    (stalk_exact : exactFunctor (Sheaf J (Type w)) (Type w)
      (topologyStalk J fiber initiallySmall)) : PointOfTopology J where
  fiber := fiber
  initiallySmall := initiallySmall
  jointly_surjective := jointly_surjective
  stalk_exact := stalk_exact

/-- The stalk functor on sheaves associated to a topology point. -/
noncomputable def sheafFiber (p : PointOfTopology J) :
    Sheaf J (Type w) ⥤ Type w :=
  topologyStalk J p.fiber p.initiallySmall

/-- The stalk functor of a topology point is the canonical stalk constructed
from its fiber functor and size witness. -/
theorem sheafFiber_eq (p : PointOfTopology J) :
    p.sheafFiber = topologyStalk J p.fiber p.initiallySmall := rfl

/-- The stalk functor of a topology point preserves finite limits. -/
@[instance] theorem preservesFiniteLimits (p : PointOfTopology J) :
    CategoryTheory.Limits.PreservesFiniteLimits p.sheafFiber := p.stalk_exact.1

/-- The stalk functor of a topology point preserves finite colimits. -/
@[instance] theorem preservesFiniteColimits (p : PointOfTopology J) :
    CategoryTheory.Limits.PreservesFiniteColimits p.sheafFiber := p.stalk_exact.2

end PointOfTopology

end CategoryTheory.GrothendieckTopology
