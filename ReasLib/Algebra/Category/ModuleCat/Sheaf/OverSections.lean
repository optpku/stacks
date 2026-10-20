/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OverSections

/-!
# Sections of module sheaves on slice categories

This leaf exposes the sheaf-level spelling of the terminal-evaluation API from
`ModuleCat/Presheaf/OverSections`.  It has no ringed-site, space, or topology-specific
assumptions beyond the sheaf carried by the input module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {U : C}
variable {J : GrothendieckTopology (Over U)} {R : Sheaf J RingCat.{w}}

/-- Sections of a module sheaf on `C / U` are equivalent to its value at the terminal object
`U ⟶ U`. -/
noncomputable def overSectionsEquivEvaluation
    (M : SheafOfModules.{z} R) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  PresheafOfModules.overSectionsEquivEvaluation M.val

/-- `overSectionsEquivEvaluation` evaluates a slice section at `U ⟶ U`. -/
@[simp]
theorem overSectionsEquivEvaluation_apply
    (M : SheafOfModules.{z} R) (s : M.sections) :
    overSectionsEquivEvaluation M s = s.1 (op (Over.mk (𝟙 U))) := sorry

/-- The inverse slice terminal-evaluation equivalence computes a reconstructed sheaf section at
an arbitrary object of `C / U`. -/
@[simp]
theorem overSectionsEquivEvaluation_symm_apply
    (M : SheafOfModules.{z} R)
    (m : M.val.obj (op (Over.mk (𝟙 U)))) (W : Over U) :
    ((overSectionsEquivEvaluation M).symm m).1 (op W) =
      M.val.map ((Over.mkIdTerminal.from W).op) m := sorry

/-- Slice terminal evaluation commutes with the map on sections induced by a module-sheaf
morphism. -/
@[simp]
theorem overSectionsEquivEvaluation_sectionsMap
    {M N : SheafOfModules.{z} R} (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivEvaluation N (sectionsMap ψ s) =
      ψ.val.app (op (Over.mk (𝟙 U))) (overSectionsEquivEvaluation M s) := sorry

/-- Reconstruction from a slice terminal value is natural in a module-sheaf morphism. -/
@[simp]
theorem sectionsMap_overSectionsEquivEvaluation_symm
    {M N : SheafOfModules.{z} R} (ψ : M ⟶ N)
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    sectionsMap ψ ((overSectionsEquivEvaluation M).symm m) =
      (overSectionsEquivEvaluation N).symm (ψ.val.app (op (Over.mk (𝟙 U))) m) := sorry

end SheafOfModules

namespace SheafOfModules

variable {D : Type u} [Category.{v} D]
variable {K : GrothendieckTopology D} {S : Sheaf K RingCat.{w}}

/-- Sections of the restriction of a module sheaf to `D / U` are equivalent to the original
module's value at `U`. -/
noncomputable def sectionsOverEquiv
    (M : SheafOfModules.{z} S) (U : D) :
    (M.over U).sections ≃ M.val.obj (op U) :=
  overSectionsEquivEvaluation (M.over U)

/-- `sectionsOverEquiv` evaluates a compatible section of `M.over U` at `U ⟶ U`. -/
@[simp]
theorem sectionsOverEquiv_apply
    (M : SheafOfModules.{z} S) (U : D) (s : (M.over U).sections) :
    sectionsOverEquiv M U s = s.1 (op (Over.mk (𝟙 U))) := sorry

/-- The inverse of `sectionsOverEquiv` evaluates at an arrow `V ⟶ U` by the ordinary restriction
map of `M`. -/
@[simp]
theorem sectionsOverEquiv_symm_apply
    (M : SheafOfModules.{z} S) {V U : D} (f : V ⟶ U)
    (m : M.val.obj (op U)) :
    ((sectionsOverEquiv M U).symm m).1 (op (Over.mk f)) = M.val.map f.op m := sorry

/-- The direct restriction-to-slice section equivalence is natural in a module-sheaf morphism. -/
@[simp]
theorem sectionsOverEquiv_sectionsMap
    {M N : SheafOfModules.{z} S} (U : D) (ψ : M ⟶ N) (s : (M.over U).sections) :
    sectionsOverEquiv N U (sectionsMap (ψ.over U) s) =
      ψ.val.app (op U) (sectionsOverEquiv M U s) := sorry

/-- Reconstructing a section of a restriction from a base-site value is natural in a
module-sheaf morphism. -/
@[simp]
theorem sectionsMap_sectionsOverEquiv_symm
    {M N : SheafOfModules.{z} S} (U : D) (ψ : M ⟶ N)
    (m : M.val.obj (op U)) :
    sectionsMap (ψ.over U) ((sectionsOverEquiv M U).symm m) =
      (sectionsOverEquiv N U).symm (ψ.val.app (op U) m) := sorry

/-- A module-sheaf morphism with an explicit right inverse induces a surjective map on global
sections. -/
theorem sectionsMap_surjective_of_comp_eq_id
    {M N : SheafOfModules.{z} S} {f : M ⟶ N} {g : N ⟶ M}
    (h : g ≫ f = 𝟙 N) : Function.Surjective (sectionsMap f) := sorry

/-- Evaluation at any object sends a module-sheaf morphism with an explicit right inverse to a
surjective linear map. -/
theorem evaluation_map_surjective_of_comp_eq_id
    {M N : SheafOfModules.{z} S} {f : M ⟶ N} {g : N ⟶ M}
    (h : g ≫ f = 𝟙 N) (U : Dᵒᵖ) :
    Function.Surjective (((evaluation S U).map f).hom) := sorry

end SheafOfModules

