module

public import ReasLib.CategoryTheory.Pro.Representative
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essential constancy of pro-system presentations

`Pro.HasValue` and its stage representatives live in `Pro.Representative`. This leaf relates
existence of a value to the presentation-level notion of an essentially constant cofiltered
diagram, without imposing unnecessary local-smallness assumptions.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe uC vC uD vD uI vI

namespace CategoryTheory

namespace Pro

variable {C : Type uC} [Category.{vC} C]

/-- A cofiltered diagram is essentially constant exactly when its pro-presentation has some
value. -/
theorem exists_hasValue_iff_essentiallyConstant
    {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    [IsCofiltered I] (F : I ⥤ C) :
    (∃ X : C, HasValue F X) ↔ IsCofiltered.IsEssentiallyConstant F := sorry

namespace HasValue

/-- A pro-value transports along an isomorphism of its value objects. -/
theorem of_iso {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    {F : I ⥤ C} {X Y : C} (h : HasValue F X) (e : X ≅ Y) :
    HasValue F Y := sorry

/-- Any two specified values of the same presentation are isomorphic. Given explicit
corepresentations, the canonical isomorphism is mathlib's
`Functor.CorepresentableBy.uniqueUpToIso`. -/
theorem nonempty_iso {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    {F : I ⥤ C} {X Y : C} (hX : HasValue F X) (hY : HasValue F Y) :
    Nonempty (X ≅ Y) :=
  let ⟨eX⟩ := hX
  let ⟨eY⟩ := hY
  ⟨eX.uniqueUpToIso eY⟩

/-- A pro-value of a cofiltered diagram implies that its presentation is essentially constant. -/
theorem essentiallyConstant {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    [IsCofiltered I] {F : I ⥤ C} {X : C} (h : HasValue F X) :
    IsCofiltered.IsEssentiallyConstant F := sorry

/-- Postcomposing a cofiltered pro-system carries a specified pro-value to the image of that
value. Cofilteredness is what makes the Hom-colimit value stable under an arbitrary functor and
avoids a new choice of value after applying it. -/
theorem map {I : Type uI} [Category.{vI} I] [Small.{vC} I] [IsCofiltered I]
    {F : I ⥤ C} {X : C} {D : Type uD} [Category.{vD} D] [Small.{vD} I]
    (h : HasValue F X) (G : C ⥤ D) :
    HasValue (F ⋙ G) (G.obj X) := sorry

end HasValue

namespace IsCofiltered.IsEssentiallyConstant

/-- An essentially constant cofiltered diagram has some pro-value. -/
theorem exists_hasValue {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    [IsCofiltered I] {F : I ⥤ C} (h : IsCofiltered.IsEssentiallyConstant F) :
    ∃ X : C, HasValue F X := sorry

end IsCofiltered.IsEssentiallyConstant

end Pro

end CategoryTheory
