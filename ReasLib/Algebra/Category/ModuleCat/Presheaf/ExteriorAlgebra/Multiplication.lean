/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on exterior-algebra presheaves

Objectwise exterior-algebra multiplication commutes with restriction and therefore assembles into
a morphism from the pointwise tensor square of the exterior-algebra presheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Objectwise exterior-algebra multiplication commutes with module-presheaf restriction maps. -/
theorem mulHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.exteriorAlgebra.mul (sectionObj O F V)) =
      ModuleCat.exteriorAlgebra.mul (sectionObj O F U) ≫ map O F i := sorry

/-- Multiplication on a sectionwise exterior-algebra presheaf. -/
@[stacks 01CF "multiplication on an exterior-algebra presheaf"]
noncomputable def mulHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F) ⟶
      presheaf O F where
  app U := ModuleCat.exteriorAlgebra.mul (sectionObj O F U)
  naturality := mulHom_app_naturality O F

/-- A component of presheaf exterior-algebra multiplication is ordinary exterior-algebra
multiplication on sections. -/
theorem mulHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (mulHom O F).app U = ModuleCat.exteriorAlgebra.mul (sectionObj O F U) := sorry

/-- Presheaf exterior-algebra multiplication acts on pure tensors by multiplying sections. -/
@[simp]
theorem mulHom_app_tmul
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ)
    (a b : ExteriorAlgebra (O.obj U) (sectionObj O F U)) :
    (mulHom O F).app U (a ⊗ₜ b) = a * b := sorry

/-- Exterior-algebra presheaf multiplication is natural in the module presheaf. -/
@[reassoc]
theorem mulHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    PresheafOfModules.Monoidal.tensorHom (hom O f) (hom O f) ≫ mulHom O G =
      mulHom O F ≫ hom O f := sorry

/-- Objectwise exterior-algebra units commute with restriction maps. -/
theorem oneHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.unit (RingPresheaf O)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.exteriorAlgebra.one (sectionObj O F V)) =
      ModuleCat.exteriorAlgebra.one (sectionObj O F U) ≫ map O F i := sorry

/-- The unit morphism of a sectionwise exterior-algebra presheaf. -/
@[stacks 01CF "unit of an exterior-algebra presheaf"]
noncomputable def oneHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    𝟙_ (PresheafOfModules.{w} (RingPresheaf O)) ⟶ presheaf O F where
  app U := ModuleCat.exteriorAlgebra.one (sectionObj O F U)
  naturality := oneHom_app_naturality O F

/-- A component of the exterior-algebra presheaf unit is the ordinary algebra unit. -/
theorem oneHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U = ModuleCat.exteriorAlgebra.one (sectionObj O F U) := sorry

/-- The exterior-algebra presheaf unit sends the section-ring unit to the algebra unit. -/
@[simp]
theorem oneHom_app_one
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U (1 : O.obj U) =
      (1 : ExteriorAlgebra (O.obj U) (sectionObj O F U)) := sorry

/-- Exterior-algebra presheaf units are natural in the module presheaf. -/
@[reassoc]
theorem oneHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    oneHom O F ≫ hom O f = oneHom O G := sorry

end PresheafOfModules.ExteriorAlgebra
