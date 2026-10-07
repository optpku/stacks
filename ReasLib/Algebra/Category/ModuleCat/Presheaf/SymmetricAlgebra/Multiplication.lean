module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra
public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on symmetric-algebra presheaves

The unit and multiplication of the sectionwise symmetric algebras commute with restriction and
therefore assemble into morphisms of module presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricAlgebra

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Objectwise symmetric-algebra multiplication commutes with restriction maps. -/
theorem mulHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.symmetricAlgebra.mul (sectionObj O F V)) =
      ModuleCat.symmetricAlgebra.mul (sectionObj O F U) ≫ map O F i := sorry

/-- Multiplication on a sectionwise symmetric-algebra presheaf. -/
@[stacks 01CF "multiplication on a symmetric-algebra presheaf"]
noncomputable def mulHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    PresheafOfModules.Monoidal.tensorObj (presheaf O F) (presheaf O F) ⟶
      presheaf O F where
  app U := ModuleCat.symmetricAlgebra.mul (sectionObj O F U)
  naturality := mulHom_app_naturality O F

/-- A component of symmetric-algebra presheaf multiplication is ordinary multiplication on
sections. -/
theorem mulHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (mulHom O F).app U = ModuleCat.symmetricAlgebra.mul (sectionObj O F U) := sorry

/-- Symmetric-algebra presheaf multiplication acts on pure tensors by multiplying sections. -/
@[simp]
theorem mulHom_app_tmul
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ)
    (a b : _root_.SymmetricAlgebra (O.obj U) (sectionObj O F U)) :
    (mulHom O F).app U (a ⊗ₜ b) = a * b := sorry

/-- Symmetric-algebra presheaf multiplication is natural in the module presheaf. -/
@[reassoc]
theorem mulHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    PresheafOfModules.Monoidal.tensorHom (hom O f) (hom O f) ≫ mulHom O G =
      mulHom O F ≫ hom O f := sorry

/-- Objectwise symmetric-algebra units commute with restriction maps. -/
theorem oneHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.unit (RingPresheaf O)).map i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map
          (ModuleCat.symmetricAlgebra.one (sectionObj O F V)) =
      ModuleCat.symmetricAlgebra.one (sectionObj O F U) ≫ map O F i := sorry

/-- The unit morphism of a sectionwise symmetric-algebra presheaf. -/
@[stacks 01CF "unit of a symmetric-algebra presheaf"]
noncomputable def oneHom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    𝟙_ (PresheafOfModules.{w} (RingPresheaf O)) ⟶ presheaf O F where
  app U := ModuleCat.symmetricAlgebra.one (sectionObj O F U)
  naturality := oneHom_app_naturality O F

/-- A component of the symmetric-algebra presheaf unit is the ordinary algebra unit. -/
theorem oneHom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U = ModuleCat.symmetricAlgebra.one (sectionObj O F U) := sorry

/-- The symmetric-algebra presheaf unit sends the section-ring unit to the algebra unit. -/
@[simp]
theorem oneHom_app_one
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (oneHom O F).app U (1 : O.obj U) =
      (1 : _root_.SymmetricAlgebra (O.obj U) (sectionObj O F U)) := sorry

/-- Symmetric-algebra presheaf units are natural in the module presheaf. -/
@[reassoc]
theorem oneHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    oneHom O F ≫ hom O f = oneHom O G := sorry

end PresheafOfModules.SymmetricAlgebra
