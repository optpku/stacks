/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on tensor-algebra presheaves

The unit and multiplication of the sectionwise tensor algebras commute with restriction and
therefore assemble into morphisms of module presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.TensorAlgebra

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Objectwise tensor-algebra multiplication commutes with restriction maps. -/
theorem mulHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.tensorAlgebra.mul (sectionObj O F V)) =
      ModuleCat.tensorAlgebra.mul (sectionObj O F U) ≫ map O F i := sorry

/-- Multiplication on a sectionwise tensor-algebra presheaf. -/
@[stacks 01CF "multiplication on a tensor-algebra presheaf"]
noncomputable def mulHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F) ⟶
      presheaf O F where
  app U := ModuleCat.tensorAlgebra.mul (sectionObj O F U)
  naturality := mulHom_app_naturality O F

/-- A component of tensor-algebra presheaf multiplication is ordinary multiplication on
sections. -/
theorem mulHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (mulHom O F).app U = ModuleCat.tensorAlgebra.mul (sectionObj O F U) := sorry

/-- Tensor-algebra presheaf multiplication acts on pure tensors by multiplying sections. -/
@[simp]
theorem mulHom_app_tmul
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ)
    (a b : TensorAlgebra (O.obj U) (sectionObj O F U)) :
    (mulHom O F).app U (a ⊗ₜ b) = a * b := sorry

/-- Tensor-algebra presheaf multiplication is natural in the module presheaf. -/
@[reassoc]
theorem mulHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    PresheafOfModules.Monoidal.tensorHom (hom O f) (hom O f) ≫ mulHom O G =
      mulHom O F ≫ hom O f := sorry

/-- Objectwise tensor-algebra units commute with restriction maps. -/
theorem oneHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.unit (RingPresheaf O)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.tensorAlgebra.one (sectionObj O F V)) =
      ModuleCat.tensorAlgebra.one (sectionObj O F U) ≫ map O F i := sorry

/-- The unit morphism of a sectionwise tensor-algebra presheaf. -/
@[stacks 01CF "unit of a tensor-algebra presheaf"]
noncomputable def oneHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    𝟙_ (PresheafOfModules.{w} (RingPresheaf O)) ⟶ presheaf O F where
  app U := ModuleCat.tensorAlgebra.one (sectionObj O F U)
  naturality := oneHom_app_naturality O F

/-- A component of the tensor-algebra presheaf unit is the ordinary algebra unit. -/
theorem oneHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U = ModuleCat.tensorAlgebra.one (sectionObj O F U) := sorry

/-- The tensor-algebra presheaf unit sends the section-ring unit to the algebra unit. -/
@[simp]
theorem oneHom_app_one
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U (1 : O.obj U) =
      (1 : TensorAlgebra (O.obj U) (sectionObj O F U)) := sorry

/-- Tensor-algebra presheaf units are natural in the module presheaf. -/
@[reassoc]
theorem oneHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    oneHom O F ≫ hom O f = oneHom O G := sorry

end PresheafOfModules.TensorAlgebra
