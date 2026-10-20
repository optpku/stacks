module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Sheaves.Stalks

@[expose] public section

open CategoryTheory CategoryTheory.Limits GrothendieckTopology TopCat TopologicalSpace

noncomputable section

namespace CofiniteTopology.GenericStalk

/-- The natural numbers equipped with the cofinite topology, as a bundled space. -/
abbrev space : TopCat.{0} := TopCat.of (CofiniteTopology ℕ)

/-- The generic fiber sends each nonempty open to a singleton and the empty open to
the empty type, with maps induced by inclusions of opens. -/
def fiber : Opens space ⥤ Type where
  obj U := ULift (PLift (Nonempty U))
  map f := ↾fun h ↦ ⟨⟨Nonempty.map (Set.inclusion (leOfHom f)) h.down.down⟩⟩
  map_id _ := ConcreteCategory.hom_ext _ _ (fun _ ↦ Subsingleton.elim _ _)
  map_comp _ _ := ConcreteCategory.hom_ext _ _ (fun _ ↦ Subsingleton.elim _ _)

/-- The generic fiber over an open is empty exactly when that open is empty. -/
theorem fiber_isEmpty_iff (U : Opens space) :
    IsEmpty (fiber.obj U) ↔ ¬ Nonempty U := sorry

/-- The category of elements of the generic fiber on the infinite cofinite space is
cofiltered. -/
instance isCofiltered : IsCofiltered fiber.Elements := sorry

/-- Covering sieves of the opens site act jointly surjectively on the generic fiber. -/
theorem jointlySurjective {U : Opens space} (R : Sieve U)
    (hR : R ∈ Opens.grothendieckTopology space U) (x : fiber.obj U) :
    ∃ (V : Opens space) (f : V ⟶ U) (_ : R f) (y : fiber.obj V), fiber.map f y = x := sorry

/-- The generic point of the opens site of the infinite cofinite space. -/
def sitePoint : Point.{0} (Opens.grothendieckTopology space) where
  fiber := fiber
  isCofiltered := isCofiltered
  initiallySmall := CategoryTheory.initiallySmall_of_essentiallySmall fiber.Elements
  jointly_surjective := jointlySurjective

/-- The sheaf-fiber functor of the generic site point of the infinite cofinite space. -/
def stalkFunctor : space.Sheaf Type ⥤ Type := sitePoint.sheafFiber

/-- The spatial stalk functor sends a sheaf to the stalk of its underlying presheaf
at the given point of the infinite cofinite space. -/
abbrev spatialStalkFunctor (x : space) : space.Sheaf Type ⥤ Type :=
  Sheaf.forget Type space ⋙ Presheaf.stalkFunctor Type x

/-- The generic stalk functor on the infinite cofinite space preserves finite limits
and finite colimits. -/
theorem exact : exactFunctor (space.Sheaf Type) Type stalkFunctor := sorry

/-- The generic stalk functor on the infinite cofinite space is not naturally
isomorphic to the spatial stalk functor at any point. -/
theorem not_isIsomorphic_spatialStalk (x : space) :
    ¬ IsIsomorphic stalkFunctor (spatialStalkFunctor x) := sorry

end CofiniteTopology.GenericStalk

end

end
