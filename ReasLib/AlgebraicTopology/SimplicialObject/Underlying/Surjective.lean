module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise surjections detected by a functor to types

This leaf owns the morphism property saying that a map of simplicial objects becomes degreewise
surjective after applying a functor to types. It is independent of any algebraic argument used to
deduce a lifting property from surjectivity.
-/

@[expose] public section

open CategoryTheory Limits

universe v u w v' u'

namespace CategoryTheory.SimplicialObject.Underlying

variable {A : Type u} [Category.{v} A]

/-- The morphism property of simplicial maps that become degreewise surjective after applying
`U : A ⥤ Type w`. -/
@[stacks 08P0 "degreewise surjections detected by an underlying functor"]
def surjections (U : A ⥤ Type w) : MorphismProperty (SimplicialObject A) :=
  ((MorphismProperty.surjective (Type w)).functorCategory SimplexCategoryᵒᵖ).inverseImage
    ((SimplicialObject.whiskering A (Type w)).obj U)

/-- Membership in `Underlying.surjections U` is pointwise surjectivity after applying `U`. -/
@[simp, stacks 08P0 "membership in the underlying degreewise-surjection property"]
theorem surjections_iff (U : A ⥤ Type w) {X Y : SimplicialObject A} (f : X ⟶ Y) :
    surjections U f ↔
      ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (U.map (f.app n)) := sorry

/-- Detecting degreewise surjections through a composite functor is the inverse image of the
property detected after the second functor. -/
@[stacks 08P0 "composition of underlying degreewise-surjection detectors"]
theorem surjections_comp
    {B : Type u'} [Category.{v'} B] (F : A ⥤ B) (U : B ⥤ Type w) :
    surjections (F ⋙ U) =
      (surjections U).inverseImage ((SimplicialObject.whiskering A B).obj F) := sorry

namespace surjections

/-- If a faithful detector preserves epimorphisms and the source has pushouts, then degreewise
surjectivity detected by it is exactly epimorphy of simplicial maps. -/
@[stacks 08P0 "underlying degreewise surjections as simplicial epimorphisms"]
theorem eq_epimorphisms (U : A ⥤ Type w) [U.Faithful] [U.PreservesEpimorphisms]
    [HasPushouts A] :
    surjections U = MorphismProperty.epimorphisms (SimplicialObject A) := sorry

end surjections

/-- Under the canonical exactness assumptions on a concrete detector, a simplicial map is an
epimorphism exactly when it is sent to a surjection in every degree. -/
@[stacks 08P0 "simplicial epimorphisms detected by degreewise surjectivity"]
theorem epi_iff_surjective (U : A ⥤ Type w) [U.Faithful] [U.PreservesEpimorphisms]
    [HasPushouts A] {X Y : SimplicialObject A} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (U.map (f.app n)) := sorry

end CategoryTheory.SimplicialObject.Underlying
