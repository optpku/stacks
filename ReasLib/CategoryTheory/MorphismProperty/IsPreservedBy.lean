module

public import Mathlib.CategoryTheory.MorphismProperty.Composition

@[expose] public section

/-!
# Functors Preserving Morphism Properties

This leaf records the reusable relation saying that a functor maps one
morphism property into another. The same-property specialization is the
standard preservation condition for an endofunctor.
-/

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- A functor maps `W` into `W'` when every morphism satisfying `W` has image
satisfying `W'`. The field is phrased using `inverseImage`, matching the
order-theoretic API for `MorphismProperty`. -/
class IsMappedBy (W : MorphismProperty C) (F : C ⥤ D)
    (W' : MorphismProperty D) : Prop where
  /-- The source property is contained in the inverse image of the target
  property. -/
  map_mem : W ≤ W'.inverseImage F

/-- An endofunctor preserves a morphism property when it maps that property
into itself. -/
abbrev IsPreservedBy (W : MorphismProperty C) (F : C ⥤ C) : Prop :=
  W.IsMappedBy F W

namespace IsMappedBy

/-- The identity functor maps every morphism property into itself. -/
instance id (W : MorphismProperty C) : W.IsMappedBy (𝟭 C) W := sorry

/-- Mapping morphism properties is closed under composition of functors. The
intermediate property is explicit because it cannot be inferred from the
composite functor and the endpoint properties alone. -/
theorem comp (W : MorphismProperty C) (W' : MorphismProperty D)
    (W'' : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
    (hF : W.IsMappedBy F W') (hG : W'.IsMappedBy G W'') :
    W.IsMappedBy (F ⋙ G) W'' := sorry

/-- Mapping is contravariant in the source property and covariant in the
target property. -/
theorem of_le {W₀ W : MorphismProperty C} {W' W'₀ : MorphismProperty D}
    {F : C ⥤ D} (h : W.IsMappedBy F W') (h₀ : W₀ ≤ W) (h' : W' ≤ W'₀) :
    W₀.IsMappedBy F W'₀ := sorry

end IsMappedBy

namespace IsPreservedBy

/-- A composite of endofunctors preserving the same morphism property again
preserves that property. -/
instance comp (W : MorphismProperty C) (F G : C ⥤ C)
    [W.IsPreservedBy F] [W.IsPreservedBy G] :
    W.IsPreservedBy (F ⋙ G) := sorry

end IsPreservedBy

end CategoryTheory.MorphismProperty
