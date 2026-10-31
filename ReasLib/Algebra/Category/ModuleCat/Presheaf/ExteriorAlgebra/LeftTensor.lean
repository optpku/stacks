/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-one multiplication on exterior-algebra presheaves

The sectionwise maps `F(U) ⊗ Λ(F(U)) ⟶ Λ(F(U))` are compatible with restriction and
therefore assemble into a morphism of module presheaves over any commutative ring presheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The objectwise degree-one exterior multiplication maps commute with restriction maps. -/
theorem leftTensorHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj F (presheaf 𝒪 F)).map i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorAlgebra.leftTensorMap (sectionObj 𝒪 F V)) =
      ModuleCat.exteriorAlgebra.leftTensorMap (sectionObj 𝒪 F U) ≫ map 𝒪 F i := sorry

/-- The sectionwise degree-one left multiplication morphism
`F ⊗ Λ(F) ⟶ Λ(F)` for a module presheaf. -/
noncomputable def leftTensorHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    PresheafOfModules.Monoidal.tensorObj F (presheaf 𝒪 F) ⟶ presheaf 𝒪 F where
  app U := ModuleCat.exteriorAlgebra.leftTensorMap (sectionObj 𝒪 F U)
  naturality := leftTensorHom_app_naturality 𝒪 F

/-- A component of the presheaf degree-one multiplication morphism is the corresponding
`ModuleCat` morphism. -/
theorem leftTensorHom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (leftTensorHom 𝒪 F).app U =
      ModuleCat.exteriorAlgebra.leftTensorMap (sectionObj 𝒪 F U) := sorry

/-- The presheaf degree-one multiplication morphism evaluates on pure tensors by multiplication
in the sectionwise exterior algebra. -/
@[simp]
theorem leftTensorHom_app_tmul
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ)
    (x : sectionObj 𝒪 F U) (a : ExteriorAlgebra (𝒪.obj U) (sectionObj 𝒪 F U)) :
    (leftTensorHom 𝒪 F).app U (x ⊗ₜ a) =
      _root_.ExteriorAlgebra.ι (𝒪.obj U) x * a := sorry

/-- Degree-one exterior multiplication is natural in the module presheaf. -/
theorem leftTensorHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    PresheafOfModules.Monoidal.tensorHom f (hom 𝒪 f) ≫ leftTensorHom 𝒪 G =
      leftTensorHom 𝒪 F ≫ hom 𝒪 f := sorry

end PresheafOfModules.ExteriorAlgebra
