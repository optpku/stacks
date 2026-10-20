module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Property

/-!
# Composition criteria for strongly cartesian morphisms

This module collects functor-composition facts about mathlib's canonical
`Functor.IsStronglyCartesian` predicate.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/-- If `φ : a ⟶ b` is strongly cartesian for `F : A ⥤ B` and its
image is strongly cartesian for `G : B ⥤ C`, then `φ` is strongly cartesian for the composite
functor `F ⋙ G`. -/
@[stacks 09WU]
theorem isStronglyCartesian_map_comp
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [F.IsStronglyCartesian (F.map φ) φ]
    [G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ)] :
    (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ := sorry
/- Proof strategy: apply the strongly cartesian universal property first to `G` and then to `F`;
the two factorization and uniqueness clauses compose. -/

/-- Strong cartesianness for a composite projection is reflected by its first
factor when the second functor is faithful. -/
@[stacks 09WU "strong cartesianness reflects along a faithful functor"]
theorem isStronglyCartesian_of_comp_of_faithful
    (F : A ⥤ B) (G : B ⥤ C) [G.Faithful]
    {a b : A} (φ : a ⟶ b)
    (hφ : (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ) :
    F.IsStronglyCartesian (F.map φ) φ := sorry

end CategoryTheory.Functor
