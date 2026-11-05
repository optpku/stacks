module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.FullSubcategory
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits.Comparison

/-!
# Comparing essentially constant values across full subcategories

This file combines three independent changes of presentation: mapping a selected essentially
constant (co)limit presentation to an ambient category, transporting it across a diagram
isomorphism, and changing indices along a final or initial functor.  The resulting comparison
isomorphisms do not require the full-subcategory inclusion to preserve arbitrary limits or
colimits.
-/

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory

open Limits

variable {I : Type uI} [Category.{vI} I]
  {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C]

namespace IsFiltered.IsEssentiallyConstant.FullSubcategory

/-- Compare the ambient image of the colimit of an essentially constant full-subcategory
diagram with the colimit of an ambient diagram presented after final reindexing.

The construction uses the selected essentially constant colimit presentation, so it does not
assume that `P.ι` preserves arbitrary colimits. -/
@[stacks 05PV "value comparison after final reindexing"]
noncomputable def colimitIsoOfFinal
    (H : I ⥤ J) [H.Final] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientColimit : HasColimit M] [restrictedColimit : HasColimit N]
    (hN : IsFiltered.IsEssentiallyConstant N) :
    P.ι.obj (colimit N) ≅ colimit M :=
  P.ι.mapIso hN.colimitIso.symm ≪≫
    IsColimit.coconePointUniqueUpToIso
      ((IsColimit.precomposeHomEquiv e
          (P.ι.mapCocone hN.colimitCocone.cocone)).symm
        ((IsFiltered.IsEssentiallyConstant.colimitCocone.isEssentiallyConstant hN).map
          P.ι).isColimit)
      (colimit.isColimit (H ⋙ M)) ≪≫
    Functor.Final.colimitIso H M

namespace colimitIsoOfFinal

/-- The forward comparison sends each full-subcategory colimit leg to the corresponding
ambient colimit leg, after applying the inverse diagram comparison. -/
@[reassoc]
theorem hom_ι
    (H : I ⥤ J) [H.Final] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientColimit : HasColimit M] [restrictedColimit : HasColimit N]
    (hN : IsFiltered.IsEssentiallyConstant N) (i : I) :
    P.ι.map (colimit.ι N i) ≫
        (colimitIsoOfFinal H e hN).hom =
      e.inv.app i ≫ colimit.ι M (H.obj i) := sorry

/-- The inverse comparison sends each ambient colimit leg to the corresponding
full-subcategory colimit leg, after applying the forward diagram comparison. -/
@[reassoc]
theorem ι_inv
    (H : I ⥤ J) [H.Final] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientColimit : HasColimit M] [restrictedColimit : HasColimit N]
    (hN : IsFiltered.IsEssentiallyConstant N) (i : I) :
    colimit.ι M (H.obj i) ≫
        (colimitIsoOfFinal H e hN).inv =
      e.hom.app i ≫ P.ι.map (colimit.ι N i) := sorry

end colimitIsoOfFinal

end IsFiltered.IsEssentiallyConstant.FullSubcategory

namespace IsCofiltered.IsEssentiallyConstant.FullSubcategory

/-- Compare the ambient image of the limit of an essentially constant full-subcategory
diagram with the limit of an ambient diagram presented after initial reindexing.

The construction uses the selected essentially constant limit presentation, so it does not
assume that `P.ι` preserves arbitrary limits. -/
@[stacks 05PV "value comparison after initial reindexing"]
noncomputable def limitIsoOfInitial
    (H : I ⥤ J) [H.Initial] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientLimit : HasLimit M] [restrictedLimit : HasLimit N]
    (hN : IsCofiltered.IsEssentiallyConstant N) :
    P.ι.obj (limit N) ≅ limit M :=
  P.ι.mapIso hN.limitIso ≪≫
    IsLimit.conePointUniqueUpToIso
      ((IsLimit.postcomposeInvEquiv e
          (P.ι.mapCone hN.limitCone.cone)).symm
        ((IsCofiltered.IsEssentiallyConstant.limitCone.isEssentiallyConstant hN).map
          P.ι).isLimit)
      (limit.isLimit (H ⋙ M)) ≪≫
    Functor.Initial.limitIso H M

namespace limitIsoOfInitial

/-- The forward comparison sends each full-subcategory limit projection to the corresponding
ambient limit projection, followed by the inverse diagram comparison. -/
@[reassoc]
theorem hom_π
    (H : I ⥤ J) [H.Initial] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientLimit : HasLimit M] [restrictedLimit : HasLimit N]
    (hN : IsCofiltered.IsEssentiallyConstant N) (i : I) :
    (limitIsoOfInitial H e hN).hom ≫
        limit.π M (H.obj i) =
      P.ι.map (limit.π N i) ≫ e.inv.app i := sorry

/-- The inverse comparison sends each ambient limit projection to the corresponding
full-subcategory limit projection, followed by the forward diagram comparison. -/
@[reassoc]
theorem inv_π
    (H : I ⥤ J) [H.Initial] {P : ObjectProperty C}
    {M : J ⥤ C} {N : I ⥤ P.FullSubcategory}
    (e : H ⋙ M ≅ N ⋙ P.ι)
    [ambientLimit : HasLimit M] [restrictedLimit : HasLimit N]
    (hN : IsCofiltered.IsEssentiallyConstant N) (i : I) :
    (limitIsoOfInitial H e hN).inv ≫
        P.ι.map (limit.π N i) =
      limit.π M (H.obj i) ≫ e.hom.app i := sorry

end limitIsoOfInitial

end IsCofiltered.IsEssentiallyConstant.FullSubcategory



end CategoryTheory
