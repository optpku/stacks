module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize.Universal

/-!
# Universe resizing and the actual universal witnesses for categorical pullbacks

The original public bilimit criterion is supplied in both directions by explicit comparison
functors and natural isomorphisms. The canonical resized square is owned by `Resize.Basic`;
the concrete lifting and comparison inverse constructions are owned by `Resize.Universal`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe vA uA vB uB vC uC vX uX

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {F : A ⥤ C} {G : B ⥤ C}

namespace Resized

/-- A general categorical square is a resized bilimit precisely when its prescribed
comparison is an equivalence. Both directions use the actual universal comparison data. -/
theorem isBilimit_iff_comparisonIsEquivalence (P : CatCommSqOver F G X) :
    Resized.IsBilimit P ↔ P.comparison.IsEquivalence := by
  constructor
  · intro h
    exact (comparisonEquivalenceOfIsBilimit P h).isEquivalence_functor
  · intro h
    letI := h
    exact isBilimitOfComparisonEquivalence P P.comparison.asEquivalence (Iso.refl _)

end Resized

namespace Resized

variable {A B C X : Type (max uA vA)} [Category.{vA} A] [Category.{vA} B]
variable [Category.{vA} C] [Category.{vA} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- In the universe-homogeneous case, the resized bilimit predicate agrees with the ordinary
`Cat`-bilimit predicate. This is an interoperability theorem, not a typeclass instance: either
predicate may be chosen as the downstream owner without creating instance-search loops. -/
theorem isBilimit_iff (P : CatCommSqOver F G X) :
    Resized.IsBilimit P ↔ P.IsBilimit := sorry

end Resized

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
