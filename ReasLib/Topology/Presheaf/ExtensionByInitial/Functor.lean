/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Presheaf.ExtensionByInitial.Basic

/-!
# Extension by initial object: functoriality

This module establishes that the presheaf extension-by-initial-object construction is functorial
in the presheaf argument. The sheaf-level functor `j!` is owned by
`ReasLib.Topology.Sheaf.ExtensionByInitial.Basic`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens
open CategoryTheory.Limits TopCat.Opens.Subspace
open scoped ZeroObject

noncomputable section

universe w v u

namespace TopCat.Presheaf.ExtensionByInitial

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [HasInitial C]

open Classical in
/-- The objectwise map induced by a morphism of presheaves under extension by initial. -/
noncomputable def homApp (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) :
    (presheaf U ℱ).obj V ⟶ (presheaf U 𝒢).obj V :=
  if hV : unop V ≤ U then
    eqToHom (presheaf_obj_eq_of_le U ℱ hV) ≫
      η.app (op (preimageOpen U (unop V))) ≫
        eqToHom (presheaf_obj_eq_of_le U 𝒢 hV).symm
  else
    eqToHom (presheaf_obj_eq_of_not_le U ℱ hV) ≫
      initial.to ((presheaf U 𝒢).obj V)

/-- On opens contained in `U`, the induced map is the original component. -/
theorem homApp_eq_of_le (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : unop V ≤ U) :
    homApp U η V =
      eqToHom (presheaf_obj_eq_of_le U ℱ hV) ≫
        η.app (op (preimageOpen U (unop V))) ≫
          eqToHom (presheaf_obj_eq_of_le U 𝒢 hV).symm := sorry

/-- Outside `U`, the induced map is the unique map from the initial object. -/
theorem homApp_eq_of_not_le (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : ¬ unop V ≤ U) :
    homApp U η V =
      eqToHom (presheaf_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((presheaf U 𝒢).obj V) := sorry

/-- The induced maps are natural in the ambient open. -/
public theorem homApp_naturality (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    (presheaf U ℱ).map i ≫ homApp U η W = homApp U η V ≫ (presheaf U 𝒢).map i := sorry

/-- The natural transformation induced by a presheaf morphism under extension by initial. -/
noncomputable def hom (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢) :
    presheaf U ℱ ⟶ presheaf U 𝒢 where
  app := homApp U η
  naturality := sorry

/-- Extension by initial preserves identity morphisms. -/
public theorem functor_map_id (U : Opens X) (ℱ : (space U).Presheaf C) :
    hom U (𝟙 ℱ) = 𝟙 (presheaf U ℱ) := sorry

/-- Extension by initial preserves composition. -/
public theorem functor_map_comp (U : Opens X) {ℱ 𝒢 ℋ : (space U).Presheaf C}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    hom U (η ≫ θ) = hom U η ≫ hom U θ := sorry

/-- Extension by initial as a functor `(space U).Presheaf C ⥤ X.Presheaf C`. -/
noncomputable def functor (U : Opens X) : (space U).Presheaf C ⥤ X.Presheaf C where
  obj := presheaf U
  map := fun η => hom U η
  map_id := functor_map_id U
  map_comp := functor_map_comp U

/-- The object of the extension-by-initial functor is its ambient presheaf construction. -/
@[simp]
theorem functor_obj (U : Opens X) (ℱ : (space U).Presheaf C) :
    (functor U).obj ℱ = presheaf U ℱ := sorry

/-- The map of the extension-by-initial functor is the natural transformation `hom`. -/
@[simp]
theorem functor_map (U : Opens X) {ℱ 𝒢 : (space U).Presheaf C} (η : ℱ ⟶ 𝒢) :
    (functor U).map η = hom U η := sorry

end TopCat.Presheaf.ExtensionByInitial

/-- Notation `jₚ!` for the presheaf-level extension-by-initial functor. -/
notation:max "jₚ! " U:max => TopCat.Presheaf.ExtensionByInitial.functor U

end

end
