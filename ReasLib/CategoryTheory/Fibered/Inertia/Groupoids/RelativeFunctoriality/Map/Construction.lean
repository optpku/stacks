module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred relative inertia maps

Relative-to-absolute inertia maps and functoriality for invertible squares of
groupoid-fibred morphisms, with computational API on total categories.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

namespace RelativeInertia

/-- Forget only the relative kernel condition, retaining the selected vertical automorphism.
This map is universe-changing only through its source and target objects, which already lie in
the common inertia-stable owner. -/
@[stacks 04Z5 "groupoid-fibred relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.relativeInertia F ⟶
      FiberedCategoryOver.Groupoids.inertia X :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.toInertia
      (FiberedCategoryOver.Groupoids.toBasedFunctor F))

namespace toInertia

/-- The underlying based functor of the groupoid-fibred relative-to-absolute inertia map is the
neutral based map. -/
@[simp]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (toInertia F) =
      BasedCategory.RelativeInertia.toInertia
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

end toInertia

/-- An invertibly commuting square of morphisms between categories fibred in groupoids induces a
map on relative inertia. The groupoid-fibration owner is a full subbicategory, so no additional
cartesian-preservation datum is required. -/
@[stacks 04Z4 "groupoid-fibred relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Groupoids.relativeInertia F₁ ⟶
      FiberedCategoryOver.Groupoids.relativeInertia F₂ :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.map
      (FiberedCategoryOver.Groupoids.toBasedFunctor G)
      (FiberedCategoryOver.Groupoids.toBasedFunctor G')
      (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm))

namespace map

/-- Forgetting the groupoid-fibration owner from a relative-inertia square map recovers the
neutral based map. -/
@[simp]
theorem toBasedFunctor
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (map G G' comm) =
      BasedCategory.RelativeInertia.map
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm) := sorry

/- Axiom audit: for `toInertia` and `map`,
`#print axioms` additionally reports `sorryAx` only through inherited based-category,
functor-law, and owner-membership proof fields; their non-Prop maps are the explicit neutral
constructions above. -/

end map

end RelativeInertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
