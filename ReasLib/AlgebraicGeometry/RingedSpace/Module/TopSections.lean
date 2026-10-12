/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Sections Determined by the Top Open

This file provides the generic conversion from a module value on the top open to the corresponding
compatible family of sections. It avoids repeating this construction in scheme-level statements
that use the notation `Γ(M, ⊤)`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The restriction morphism from the top open to an arbitrary open. -/
abbrev topOpenRestriction (U : (Opens X)ᵒᵖ) :
    Opposite.op (⊤ : Opens X) ⟶ U :=
  (homOfLE (le_top : U.unop ≤ (⊤ : Opens X))).op

/-- Restricting a top-open module value along `topOpenRestriction` is compatible with all further
restrictions. -/
theorem sectionFromTop_naturality
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    ∀ U V : (Opens X)ᵒᵖ, ∀ f : U ⟶ V,
      M.val.map f (M.val.map (topOpenRestriction U) m) =
        M.val.map (topOpenRestriction V) m := sorry

/-- The compatible global section determined by a value of a module sheaf on the top open. -/
noncomputable def sectionFromTop
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.val.map (topOpenRestriction U) m)
    (sectionFromTop_naturality M m)

/-- Evaluating `sectionFromTop` on an open is restriction of its defining top-open value. -/
@[simp]
theorem sectionFromTop_eval
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) (U : (Opens X)ᵒᵖ) :
    (sectionFromTop M m).1 U = M.val.map (topOpenRestriction U) m := sorry

/-- Evaluation at the top open recovers the value used to define `sectionFromTop`. -/
@[simp]
theorem sectionFromTop_eval_top
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    (sectionFromTop M m).1 (Opposite.op ⊤) = m := sorry

/-- A compatible global section is reconstructed from its value at the top open. -/
@[simp]
theorem sectionFromTop_of_section
    (M : X.Modules) (s : M.sections) :
    sectionFromTop M (s.1 (Opposite.op ⊤)) = s := sorry

/-- Forming a compatible section from a top-open value commutes with a morphism of module
sheaves. -/
@[simp]
theorem sectionsMap_sectionFromTop
    {M N : X.Modules} (f : M ⟶ N) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    SheafOfModules.sectionsMap f (sectionFromTop M m) =
      sectionFromTop N (f.val.app (Opposite.op ⊤) m) := sorry

/-- Global sections of a module sheaf are equivalent to values over the top open. -/
noncomputable def sectionsEquivTop (M : X.Modules) :
    M.sections ≃ M.val.presheaf.obj (Opposite.op ⊤) where
  toFun s := s.1 (Opposite.op ⊤)
  invFun := sectionFromTop M
  left_inv := sectionFromTop_of_section M
  right_inv := sectionFromTop_eval_top M

/-- `sectionsEquivTop` sends a compatible section to its value at the top open. -/
@[simp]
theorem sectionsEquivTop_apply (M : X.Modules) (s : M.sections) :
    sectionsEquivTop M s = s.1 (Opposite.op ⊤) := sorry

/-- The inverse of `sectionsEquivTop` reconstructs the compatible section from a top-open value. -/
@[simp]
theorem sectionsEquivTop_symm_apply
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    (sectionsEquivTop M).symm m = sectionFromTop M m := sorry

/-- Top evaluation commutes with the map on sections induced by a morphism of module sheaves. -/
@[simp]
theorem sectionsEquivTop_sectionsMap
    {M N : X.Modules} (f : M ⟶ N) (s : M.sections) :
    sectionsEquivTop N (SheafOfModules.sectionsMap f s) =
      f.val.app (Opposite.op ⊤) (sectionsEquivTop M s) := sorry

/-- The morphism from the structure module classified by a value of a module sheaf on the top
open. -/
noncomputable def topSectionMorphism
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionFromTop M m)

/-- Applying `unitHomEquiv` to `topSectionMorphism` recovers its defining global section. -/
@[simp]
theorem unitHomEquiv_topSectionMorphism
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    M.unitHomEquiv (topSectionMorphism M m) = sectionFromTop M m := sorry

/-- Evaluating the morphism classified by a top-open value on the distinguished unit section
recovers that value. -/
@[simp]
theorem topSectionMorphism_apply_top
    (M : X.Modules) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    (topSectionMorphism M m).val.app (Opposite.op ⊤)
        (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)) = m := sorry

/-- Passing from a section to its top-open value and then to its classified unit morphism agrees
with the standard section-to-unit-morphism equivalence. -/
@[simp]
theorem topSectionMorphism_sectionsEquivTop
    (M : X.Modules) (s : M.sections) :
    topSectionMorphism M (sectionsEquivTop M s) = M.unitHomEquiv.symm s := sorry

/-- The unit morphism classified by a top-open value is natural in the module sheaf. -/
@[simp]
theorem topSectionMorphism_map
    {M N : X.Modules} (f : M ⟶ N) (m : M.val.presheaf.obj (Opposite.op ⊤)) :
    topSectionMorphism N (f.val.app (Opposite.op ⊤) m) =
      topSectionMorphism M m ≫ f := sorry

/-- The morphism from the structure module classified by a top-open value is injective in that
value. -/
theorem topSectionMorphism_injective (M : X.Modules) :
    Function.Injective (topSectionMorphism M) := sorry

/-- The zero top-open value classifies the zero morphism from the structure module. -/
@[simp]
theorem topSectionMorphism_zero (M : X.Modules) :
    topSectionMorphism M 0 = 0 := sorry

/-- Addition of top-open values corresponds to addition of their classified structure-module
morphisms. -/
@[simp]
theorem topSectionMorphism_add
    (M : X.Modules) (m n : M.val.presheaf.obj (Opposite.op ⊤)) :
    topSectionMorphism M (m + n) = topSectionMorphism M m + topSectionMorphism M n := sorry

/-- The value of the distinguished global unit section on the top open. -/
noncomputable def unitTopValue (X : RingedSpace.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).val.presheaf.obj (Opposite.op ⊤) :=
  (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))

/-- The compatible section of the structure module determined by a top-open ring value. -/
noncomputable def unitSectionFromTop (X : RingedSpace.{u})
    (r : X.ringCatSheaf.obj.obj (Opposite.op ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  sectionFromTop (SheafOfModules.unit X.ringCatSheaf) r

/-- Top evaluation of `unitSectionFromTop` recovers the specified ring value. -/
@[simp]
theorem sectionsEquivTop_unitSectionFromTop (X : RingedSpace.{u})
    (r : X.ringCatSheaf.obj.obj (Opposite.op ⊤)) :
    sectionsEquivTop (SheafOfModules.unit X.ringCatSheaf) (unitSectionFromTop X r) = r := sorry

/-- The distinguished unit value classifies the identity of the structure module. -/
@[simp]
theorem topSectionMorphism_unit_one :
    topSectionMorphism (SheafOfModules.unit X.ringCatSheaf)
        (unitTopValue X) =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) := sorry

end AlgebraicGeometry.RingedSpace
