module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive structure on sections of module presheaves

Compatible sections of a module presheaf form an additive commutative group under pointwise
operations.  This file exposes that structure directly on `PresheafOfModules.sections`, together
with the evaluation and functoriality API needed by sheaf-level consumers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- Compatible sections of a module presheaf carry the pointwise additive commutative group
structure. -/
@[stacks 01BL "additive group of module-presheaf sections", instance]
noncomputable instance instSectionsAddCommGroup (M : PresheafOfModules.{z} R) :
    AddCommGroup M.sections :=
  @AddSubgroup.toAddCommGroup (∀ X, M.presheaf.obj X) _
    (AddGrpCat.sectionsAddSubgroup
      (M.presheaf ⋙ forget₂ AddCommGrpCat.{z} AddGrpCat.{z}))

namespace sections

variable (M : PresheafOfModules.{z} R)

/-- The zero section evaluates to zero at every object. -/
@[simp]
theorem zero_eval (X : Cᵒᵖ) : (0 : M.sections).val X = 0 := sorry

/-- Addition of sections is evaluated pointwise. -/
@[simp]
theorem add_eval (s t : M.sections) (X : Cᵒᵖ) :
    (s + t).val X = s.val X + t.val X := sorry

/-- Negation of sections is evaluated pointwise. -/
@[simp]
theorem neg_eval (s : M.sections) (X : Cᵒᵖ) :
    (-s).val X = -s.val X := sorry

end sections

/-- The map on sections induced by a module-presheaf morphism preserves zero. -/
@[simp]
theorem sectionsMap_zero {M N : PresheafOfModules.{z} R} (f : M ⟶ N) :
    sectionsMap f (0 : M.sections) = 0 := sorry

/-- The map on sections induced by a module-presheaf morphism preserves addition. -/
@[simp]
theorem sectionsMap_add {M N : PresheafOfModules.{z} R}
    (f : M ⟶ N) (s t : M.sections) :
    sectionsMap f (s + t) = sectionsMap f s + sectionsMap f t := sorry

/-- The map on sections induced by a module-presheaf morphism preserves negation. -/
@[simp]
theorem sectionsMap_neg {M N : PresheafOfModules.{z} R}
    (f : M ⟶ N) (s : M.sections) :
    sectionsMap f (-s) = -sectionsMap f s := sorry

end PresheafOfModules
