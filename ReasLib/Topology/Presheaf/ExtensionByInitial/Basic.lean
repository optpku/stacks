/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.Topology.Opens.Subspace

/-!
# Extension by initial object: presheaf-level construction

Given an open subset `U` of a topological space `X` and a presheaf `ℱ` on `U`, the
extension-by-initial-object `jₚ!(ℱ)` is the presheaf on `X` defined by:
- On `V ⊆ U`: the original sections `ℱ(V ∩ U)` (which is just `ℱ(V)` via the subspace topology)
- On `V ⊄ U`: the initial object `⊥`

This module constructs the presheaf and its functoriality. The sheaf-level construction
(sheafification of `jₚ!`) is in `Topology.Sheaf.ExtensionByInitial`.
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
/-- The value of extension-by-initial on an ambient open `V`:
sections of `ℱ` on the preimage if `V ≤ U`, otherwise the initial object. -/
public abbrev value (U : Opens X) (ℱ : (space U).Presheaf C) (V : (Opens X)ᵒᵖ) : C :=
  if unop V ≤ U then
    ℱ.obj (op (preimageOpen U (unop V)))
  else
    ⊥_ C

/-- On an ambient open contained in `U`, the value is the original section object. -/
public theorem value_eq_of_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (hV : unop V ≤ U) :
    value U ℱ V = ℱ.obj (op (preimageOpen U (unop V))) :=
  if_pos hV

/-- On an ambient open not contained in `U`, the value is the initial object. -/
public theorem value_eq_of_not_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (hV : ¬ unop V ≤ U) :
    value U ℱ V = ⊥_ C :=
  if_neg hV

open Classical in
/-- The restriction map in extension-by-initial. -/
public noncomputable def map (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    value U ℱ V ⟶ value U ℱ W :=
  if hV : unop V ≤ U then
    let hW : unop W ≤ U := le_trans i.unop.le hV
    eqToHom (value_eq_of_le U ℱ hV) ≫
      ℱ.map ((Opens.map (inclusion U)).map i.unop).op ≫
        eqToHom (value_eq_of_le U ℱ hW).symm
  else
    eqToHom (value_eq_of_not_le U ℱ hV) ≫ initial.to (value U ℱ W)

/-- The restriction maps satisfy the identity law. -/
public theorem map_id (U : Opens X) (ℱ : (space U).Presheaf C) (V : (Opens X)ᵒᵖ) :
    map U ℱ (𝟙 V) = 𝟙 (value U ℱ V) := sorry

/-- The restriction maps satisfy the composition law. -/
public theorem map_comp (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W Z : (Opens X)ᵒᵖ} (i : V ⟶ W) (j : W ⟶ Z) :
    map U ℱ (i ≫ j) = map U ℱ i ≫ map U ℱ j := sorry

/-- The ambient presheaf underlying extension by the initial object. -/
noncomputable def presheaf (U : Opens X) (ℱ : (space U).Presheaf C) : X.Presheaf C where
  obj := value U ℱ
  map := fun i => map U ℱ i
  map_id := map_id U ℱ
  map_comp := map_comp U ℱ

/-- Over an ambient open contained in `U`, the presheaf recovers the original section object. -/
theorem presheaf_obj_eq_of_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : unop V ≤ U) :
    (presheaf U ℱ).obj V = ℱ.obj (op (preimageOpen U (unop V))) :=
  value_eq_of_le U ℱ h

/-- Over an ambient open not contained in `U`, the presheaf takes the initial value. -/
theorem presheaf_obj_eq_of_not_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : ¬ unop V ≤ U) :
    (presheaf U ℱ).obj V = ⊥_ C :=
  value_eq_of_not_le U ℱ h

/-- On opens `W ⊆ V ⊆ U`, the restriction map is the original restriction map up to
canonical identifications. -/
theorem presheaf_map_eq_of_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : unop V ≤ U) :
    (presheaf U ℱ).map i =
      eqToHom (presheaf_obj_eq_of_le U ℱ hV) ≫
        ℱ.map ((Opens.map (inclusion U)).map i.unop).op ≫
          eqToHom (presheaf_obj_eq_of_le U ℱ (le_trans i.unop.le hV)).symm := sorry

/-- Outside `U`, the restriction map is the unique map from the initial object. -/
theorem presheaf_map_eq_of_not_le (U : Opens X) (ℱ : (space U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : ¬ unop V ≤ U) :
    (presheaf U ℱ).map i =
      eqToHom (presheaf_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((presheaf U ℱ).obj W) := sorry

end TopCat.Presheaf.ExtensionByInitial

end

end
