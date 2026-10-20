module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits

/-!
# Comparing selected essentially constant values with chosen (co)limits

An essentially constant presentation supplies an explicit colimit cocone or limit cone. This
file compares its selected apex with mathlib's chosen `colimit` or `limit` and records the
component formulas needed by downstream calculations.
-/

@[expose] public section

open CategoryTheory.Limits

universe uI vI uC vC

namespace CategoryTheory

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

namespace IsFiltered.IsEssentiallyConstant

/-- The canonical comparison from the apex selected by an essentially constant presentation to
mathlib's chosen colimit. -/
noncomputable def colimitIso {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M)
    [HasColimit M] :
    hM.colimitCocone.cocone.pt ≅ colimit M :=
  (colimit.isoColimitCocone hM.colimitCocone).symm

namespace colimitIso

/-- The forward selected-to-chosen colimit comparison carries each selected cocone leg to the
chosen colimit leg. -/
@[reassoc (attr := simp)]
theorem hom_ι {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M)
    [HasColimit M] (i : I) :
    hM.colimitCocone.cocone.ι.app i ≫ hM.colimitIso.hom = colimit.ι M i := sorry

/-- The inverse chosen-to-selected colimit comparison carries each chosen colimit leg to the
selected cocone leg. -/
@[reassoc (attr := simp)]
theorem ι_inv {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M)
    [HasColimit M] (i : I) :
    colimit.ι M i ≫ hM.colimitIso.inv = hM.colimitCocone.cocone.ι.app i := sorry

end colimitIso

end IsFiltered.IsEssentiallyConstant

namespace IsCofiltered.IsEssentiallyConstant

/-- The canonical comparison from mathlib's chosen limit to the apex selected by an essentially
constant presentation. -/
noncomputable def limitIso {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M)
    [HasLimit M] :
    limit M ≅ hM.limitCone.cone.pt :=
  limit.isoLimitCone hM.limitCone

namespace limitIso

/-- The forward chosen-to-selected limit comparison carries each selected projection to the
chosen limit projection. -/
@[reassoc (attr := simp)]
theorem hom_π {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M)
    [HasLimit M] (i : I) :
    hM.limitIso.hom ≫ hM.limitCone.cone.π.app i = limit.π M i := sorry

/-- The inverse selected-to-chosen limit comparison carries each chosen projection to the
selected cone projection. -/
@[reassoc (attr := simp)]
theorem inv_π {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M)
    [HasLimit M] (i : I) :
    hM.limitIso.inv ≫ limit.π M i = hM.limitCone.cone.π.app i := sorry

end limitIso

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory


