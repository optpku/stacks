module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Transport

/-!
# Essentially constant diagrams in retract-closed full subcategories

For a retract-closed object property, essential constancy can be checked after applying the
fully faithful inclusion of its full subcategory.  The split distinguished leg makes the ambient
presentation vertex a retract of a diagram object, so retract closure is exactly the needed
hypothesis.
-/

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory

open Limits

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C]

namespace Limits.Cocone.IsEssentiallyConstant

/-- The vertex of an essentially constant cocone belongs to a retract-closed object property
whenever every object of the diagram does. -/
theorem pt_mem (P : ObjectProperty C) [P.IsStableUnderRetracts]
    {M : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant)
    (hM : ∀ i : I, P (M.obj i)) :
    P c.pt := sorry

end Limits.Cocone.IsEssentiallyConstant

namespace Limits.Cone.IsEssentiallyConstant

/-- The vertex of an essentially constant cone belongs to a retract-closed object property
whenever every object of the diagram does. -/
theorem pt_mem (P : ObjectProperty C) [P.IsStableUnderRetracts]
    {M : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant)
    (hM : ∀ i : I, P (M.obj i)) :
    P c.pt := sorry

end Limits.Cone.IsEssentiallyConstant

namespace Limits.Cocone

namespace liftFullSubcategory

/-- Naturality of the explicitly lifted legs of an ambient cocone. -/
theorem naturality (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cocone (M ⋙ P.ι)) (hc : P c.pt) {i j : I} (f : i ⟶ j) :
    M.map f ≫ ObjectProperty.homMk (P := P) (X := M.obj j)
        (Y := ⟨c.pt, hc⟩) (c.ι.app j) =
      ObjectProperty.homMk (P := P) (X := M.obj i)
          (Y := ⟨c.pt, hc⟩) (c.ι.app i) ≫
        ((Functor.const I).obj (⟨c.pt, hc⟩ : P.FullSubcategory)).map f := sorry

end liftFullSubcategory

/-- Lift an ambient cocone whose vertex lies in `P` to the full subcategory of `P`.
Its object and morphism data are inherited verbatim from the ambient cocone. -/
def liftFullSubcategory (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cocone (M ⋙ P.ι)) (hc : P c.pt) :
    Cocone M where
  pt := ⟨c.pt, hc⟩
  ι :=
    { app := fun i ↦ ObjectProperty.homMk (c.ι.app i)
      naturality := fun _ _ f ↦ liftFullSubcategory.naturality P c hc f }

namespace liftFullSubcategory

/-- The lifted cocone has the prescribed ambient vertex. -/
theorem pt_obj (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cocone (M ⋙ P.ι)) (hc : P c.pt) :
    (liftFullSubcategory P c hc).pt.obj = c.pt := sorry

/-- Each lifted cocone leg is the corresponding ambient cocone leg. -/
theorem ι_app_hom (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cocone (M ⋙ P.ι)) (hc : P c.pt) (i : I) :
    ((liftFullSubcategory P c hc).ι.app i).hom = c.ι.app i := sorry

end liftFullSubcategory

end Limits.Cocone

namespace Limits.Cone

namespace liftFullSubcategory

/-- Naturality of the explicitly lifted legs of an ambient cone. -/
theorem naturality (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cone (M ⋙ P.ι)) (hc : P c.pt) {i j : I} (f : i ⟶ j) :
    ((Functor.const I).obj (⟨c.pt, hc⟩ : P.FullSubcategory)).map f ≫
        ObjectProperty.homMk (P := P) (X := ⟨c.pt, hc⟩)
          (Y := M.obj j) (c.π.app j) =
      ObjectProperty.homMk (P := P) (X := ⟨c.pt, hc⟩)
          (Y := M.obj i) (c.π.app i) ≫ M.map f := sorry

end liftFullSubcategory

/-- Lift an ambient cone whose vertex lies in `P` to the full subcategory of `P`.
Its object and morphism data are inherited verbatim from the ambient cone. -/
def liftFullSubcategory (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cone (M ⋙ P.ι)) (hc : P c.pt) :
    Cone M where
  pt := ⟨c.pt, hc⟩
  π :=
    { app := fun i ↦ ObjectProperty.homMk (c.π.app i)
      naturality := fun _ _ f ↦ liftFullSubcategory.naturality P c hc f }

namespace liftFullSubcategory

/-- The lifted cone has the prescribed ambient vertex. -/
theorem pt_obj (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cone (M ⋙ P.ι)) (hc : P c.pt) :
    (liftFullSubcategory P c hc).pt.obj = c.pt := sorry

/-- Each lifted cone leg is the corresponding ambient cone leg. -/
theorem π_app_hom (P : ObjectProperty C) {M : I ⥤ P.FullSubcategory}
    (c : Cone (M ⋙ P.ι)) (hc : P c.pt) (i : I) :
    ((liftFullSubcategory P c hc).π.app i).hom = c.π.app i := sorry

end liftFullSubcategory

end Limits.Cone

namespace IsFiltered.IsEssentiallyConstant.FullSubcategory

/-- Reflect essential constancy through the inclusion of a retract-closed full subcategory. -/
theorem of_comp_ι (P : ObjectProperty C) [P.IsStableUnderRetracts]
    {M : I ⥤ P.FullSubcategory}
    (hM : IsFiltered.IsEssentiallyConstant (M ⋙ P.ι)) :
    IsFiltered.IsEssentiallyConstant M := sorry

/-- A filtered-oriented diagram in a retract-closed full subcategory is essentially constant
exactly when its underlying ambient diagram is. -/
@[stacks 05PV "essential constancy in a retract-closed full subcategory"]
theorem comp_ι_iff (P : ObjectProperty C) [P.IsStableUnderRetracts]
    (M : I ⥤ P.FullSubcategory) :
    IsFiltered.IsEssentiallyConstant (M ⋙ P.ι) ↔
      IsFiltered.IsEssentiallyConstant M := sorry

/-- Compare essential constancy across final reindexing and a retract-closed full-subcategory
inclusion in a single reusable step. -/
theorem iff_of_final {J : Type uJ} [Category.{vJ} J] [IsFiltered I]
    (H : I ⥤ J) [H.Final] (P : ObjectProperty C) [P.IsStableUnderRetracts]
    (M : J ⥤ C) (N : I ⥤ P.FullSubcategory)
    (e : H ⋙ M ≅ N ⋙ P.ι) :
    IsFiltered.IsEssentiallyConstant M ↔
      IsFiltered.IsEssentiallyConstant N := sorry

end IsFiltered.IsEssentiallyConstant.FullSubcategory

namespace IsCofiltered.IsEssentiallyConstant.FullSubcategory

/-- Reflect cofiltered essential constancy through the inclusion of a retract-closed full
subcategory. -/
theorem of_comp_ι (P : ObjectProperty C) [P.IsStableUnderRetracts]
    {M : I ⥤ P.FullSubcategory}
    (hM : IsCofiltered.IsEssentiallyConstant (M ⋙ P.ι)) :
    IsCofiltered.IsEssentiallyConstant M := sorry

/-- A cofiltered-oriented diagram in a retract-closed full subcategory is essentially constant
exactly when its underlying ambient diagram is. -/
@[stacks 05PV "cofiltered essential constancy in a retract-closed full subcategory"]
theorem comp_ι_iff (P : ObjectProperty C) [P.IsStableUnderRetracts]
    (M : I ⥤ P.FullSubcategory) :
    IsCofiltered.IsEssentiallyConstant (M ⋙ P.ι) ↔
      IsCofiltered.IsEssentiallyConstant M := sorry

/-- Compare cofiltered essential constancy across initial reindexing and a retract-closed
full-subcategory inclusion in a single reusable step. -/
theorem iff_of_initial {J : Type uJ} [Category.{vJ} J] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] (P : ObjectProperty C) [P.IsStableUnderRetracts]
    (M : J ⥤ C) (N : I ⥤ P.FullSubcategory)
    (e : H ⋙ M ≅ N ⋙ P.ι) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant N := sorry

end IsCofiltered.IsEssentiallyConstant.FullSubcategory




end CategoryTheory
