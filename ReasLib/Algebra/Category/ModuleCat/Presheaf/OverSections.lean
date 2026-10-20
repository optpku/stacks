/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
public import ReasLib.CategoryTheory.Functor.SectionsTerminal

/-!
# Sections of module presheaves on categories with a terminal object

This leaf specializes the topology-free terminal-evaluation description in
`CategoryTheory.Functor.SectionsTerminal` to module presheaves. The main construction applies to
an arbitrary `RingCat`-valued presheaf on any category with a chosen terminal object; the
slice-site spelling is a thin specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- Compatible sections of a module presheaf are determined by their value at a terminal object. -/
noncomputable def sectionsEquivTerminal
    (M : PresheafOfModules.{z} R) (T : C) (hT : IsTerminal T) :
    M.sections ≃ M.obj (op T) :=
  CategoryTheory.Functor.sectionsEquivTerminal
    (M.presheaf ⋙ CategoryTheory.forget _) T hT

/-- `sectionsEquivTerminal` evaluates a compatible section at the chosen terminal object. -/
@[simp]
theorem sectionsEquivTerminal_apply
    (M : PresheafOfModules.{z} R) (T : C) (hT : IsTerminal T) (s : M.sections) :
    sectionsEquivTerminal M T hT s = s.1 (op T) := sorry

/-- The inverse terminal-evaluation equivalence reconstructs a section by restriction from the
terminal value. -/
@[simp]
theorem sectionsEquivTerminal_symm_apply
    (M : PresheafOfModules.{z} R) (T : C) (hT : IsTerminal T)
    (m : M.obj (op T)) (X : C) :
    ((sectionsEquivTerminal M T hT).symm m).1 (op X) =
      M.map ((hT.from X).op) m := sorry

/-- Terminal evaluation commutes with the map on compatible sections induced by a module-presheaf
morphism. -/
@[simp]
theorem sectionsEquivTerminal_sectionsMap
    {M N : PresheafOfModules.{z} R} (T : C) (hT : IsTerminal T)
    (ψ : M ⟶ N) (s : M.sections) :
    sectionsEquivTerminal N T hT (sectionsMap ψ s) =
      ψ.app (op T) (sectionsEquivTerminal M T hT s) := sorry

/-- Reconstructing a section from a terminal value is natural in a module-presheaf morphism. -/
@[simp]
theorem sectionsMap_sectionsEquivTerminal_symm
    {M N : PresheafOfModules.{z} R} (T : C) (hT : IsTerminal T)
    (ψ : M ⟶ N) (m : M.obj (op T)) :
    sectionsMap ψ ((sectionsEquivTerminal M T hT).symm m) =
      (sectionsEquivTerminal N T hT).symm (ψ.app (op T) m) := sorry

section Over

variable {U : C} {Rover : (Over U)ᵒᵖ ⥤ RingCat.{w}}

/-- Sections of a module presheaf on `C / U` are equivalent to its value at the terminal object
`U ⟶ U`. -/
noncomputable def overSectionsEquivEvaluation
    (M : PresheafOfModules.{z} Rover) :
    M.sections ≃ M.obj (op (Over.mk (𝟙 U))) :=
  sectionsEquivTerminal M (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- `overSectionsEquivEvaluation` evaluates a slice section at `U ⟶ U`. -/
@[simp]
theorem overSectionsEquivEvaluation_apply
    (M : PresheafOfModules.{z} Rover) (s : M.sections) :
    overSectionsEquivEvaluation M s = s.1 (op (Over.mk (𝟙 U))) := sorry

/-- The inverse slice terminal-evaluation equivalence computes a reconstructed section at an
arbitrary object of `C / U`. -/
@[simp]
theorem overSectionsEquivEvaluation_symm_apply
    (M : PresheafOfModules.{z} Rover)
    (m : M.obj (op (Over.mk (𝟙 U)))) (W : Over U) :
    ((overSectionsEquivEvaluation M).symm m).1 (op W) =
      M.map ((Over.mkIdTerminal.from W).op) m := sorry

/-- Slice terminal evaluation commutes with the map on sections induced by a module-presheaf
morphism. -/
@[simp]
theorem overSectionsEquivEvaluation_sectionsMap
    {M N : PresheafOfModules.{z} Rover} (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivEvaluation N (sectionsMap ψ s) =
      ψ.app (op (Over.mk (𝟙 U))) (overSectionsEquivEvaluation M s) := sorry

/-- Reconstruction from a slice terminal value is natural in a module-presheaf morphism. -/
@[simp]
theorem sectionsMap_overSectionsEquivEvaluation_symm
    {M N : PresheafOfModules.{z} Rover} (ψ : M ⟶ N)
    (m : M.obj (op (Over.mk (𝟙 U)))) :
    sectionsMap ψ ((overSectionsEquivEvaluation M).symm m) =
      (overSectionsEquivEvaluation N).symm (ψ.app (op (Over.mk (𝟙 U))) m) := sorry

end Over

end PresheafOfModules

namespace PresheafOfModules

variable {D : Type u} [Category.{v} D] {R : Dᵒᵖ ⥤ RingCat.{w}}

/-- Sections of the restriction of a module presheaf to `D / U` are equivalent to the original
module's value at `U`. -/
noncomputable def sectionsOverEquiv
    (M : PresheafOfModules.{z} R) (U : D) :
    (M.over U).sections ≃ M.obj (op U) :=
  overSectionsEquivEvaluation (M.over U)

/-- `sectionsOverEquiv` evaluates a compatible section of `M.over U` at `U ⟶ U`. -/
@[simp]
theorem sectionsOverEquiv_apply
    (M : PresheafOfModules.{z} R) (U : D) (s : (M.over U).sections) :
    sectionsOverEquiv M U s = s.1 (op (Over.mk (𝟙 U))) := sorry

/-- The inverse of `sectionsOverEquiv` evaluates at an arrow `V ⟶ U` by the ordinary restriction
map of `M`. -/
@[simp]
theorem sectionsOverEquiv_symm_apply
    (M : PresheafOfModules.{z} R) {V U : D} (f : V ⟶ U)
    (m : M.obj (op U)) :
    ((sectionsOverEquiv M U).symm m).1 (op (Over.mk f)) = M.map f.op m := sorry

/-- The direct restriction-to-slice section equivalence is natural in a module-presheaf morphism.
-/
@[simp]
theorem sectionsOverEquiv_sectionsMap
    {M N : PresheafOfModules.{z} R} (U : D) (ψ : M ⟶ N) (s : (M.over U).sections) :
    sectionsOverEquiv N U (sectionsMap (ψ.over U) s) =
      ψ.app (op U) (sectionsOverEquiv M U s) := sorry

/-- Reconstructing a section of a restriction from a base-site value is natural in a
module-presheaf morphism. -/
@[simp]
theorem sectionsMap_sectionsOverEquiv_symm
    {M N : PresheafOfModules.{z} R} (U : D) (ψ : M ⟶ N)
    (m : M.obj (op U)) :
    sectionsMap (ψ.over U) ((sectionsOverEquiv M U).symm m) =
      (sectionsOverEquiv N U).symm (ψ.app (op U) m) := sorry

end PresheafOfModules
