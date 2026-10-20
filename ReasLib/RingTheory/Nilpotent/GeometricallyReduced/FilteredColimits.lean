module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered Colimits of Geometrically Reduced Algebras

The closure statement is formulated for an arbitrary filtered-or-empty indexing
category.  This is the categorical form needed by downstream constructions;
ordered directed systems are a specialization rather than the owner API.

@stack 030T
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace Algebra.IsGeometricallyReduced

/-- Categorical owner for Lemma 10.43.2 (Tag 030T): a filtered colimit of
geometrically reduced commutative algebras is geometrically reduced.  This
cocone-level owner applies to any chosen filtered-colimit presentation; use
`colimit_of_isFilteredOrEmpty` for the
canonical colimit convenience API (including an empty diagram). -/
@[stacks 030T "cocone-level filtered-colimit owner"]
theorem of_isColimit_filtered
    {R : Type u} {J : Type v} [CommRing R]
    [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{max u v} R) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, Algebra.IsGeometricallyReduced R (F.obj j)) :
    Algebra.IsGeometricallyReduced R c.pt := sorry

/-- Lemma 10.43.2 (Tag 030T): filtered colimits of geometrically reduced commutative algebras
remain geometrically reduced.  The `IsFilteredOrEmpty` formulation includes the empty diagram. -/
@[stacks 030T]
theorem colimit_of_isFilteredOrEmpty
    {R : Type u} {I : Type v} [CommRing R]
    [Category.{v} I] [IsFilteredOrEmpty I]
    (F : I ⥤ CommAlgCat.{u} R)
    [HasColimit F]
    (hF : ∀ i, Algebra.IsGeometricallyReduced R (F.obj i)) :
    Algebra.IsGeometricallyReduced R (colimit F : CommAlgCat.{u} R) := sorry

end Algebra.IsGeometricallyReduced
