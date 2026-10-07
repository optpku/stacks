module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of exterior-power presheaves

The fixed-degree exterior products on section modules commute with restriction and assemble into
presheaf morphisms `Λ^n(F) ⊗ Λ^m(F) ⟶ Λ^(n + m)(F)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The objectwise exterior products commute with restriction maps. -/
theorem mulHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (presheaf 𝒪 F n) (presheaf 𝒪 F m)).map i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorPower.mul (sectionObj 𝒪 F V) n m) =
      ModuleCat.exteriorPower.mul (sectionObj 𝒪 F U) n m ≫ map 𝒪 F (n + m) i := sorry

/-- The multiplication morphism
`Λ^n(F) ⊗ Λ^m(F) ⟶ Λ^(n + m)(F)` for a module presheaf. -/
@[stacks 01CF "multiplication of exterior-power presheaves"]
noncomputable def mulHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (presheaf 𝒪 F n) (presheaf 𝒪 F m) ⟶
      presheaf 𝒪 F (n + m) where
  app U := ModuleCat.exteriorPower.mul (sectionObj 𝒪 F U) n m
  naturality := mulHom_app_naturality 𝒪 F n m

/-- A component of the exterior-power presheaf multiplication is the corresponding
`ModuleCat` multiplication. -/
theorem mulHom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) (U : Cᵒᵖ) :
    (mulHom 𝒪 F n m).app U =
      ModuleCat.exteriorPower.mul (sectionObj 𝒪 F U) n m := sorry

/-- Presheaf exterior multiplication concatenates alternating generators sectionwise. -/
@[simp]
theorem mulHom_app_tmul_mk
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) (U : Cᵒᵖ)
    (x : Fin n → sectionObj 𝒪 F U) (y : Fin m → sectionObj 𝒪 F U) :
    (mulHom 𝒪 F n m).app U
        (ModuleCat.exteriorPower.mk x ⊗ₜ ModuleCat.exteriorPower.mk y) =
      ModuleCat.exteriorPower.mk (Fin.append x y) := sorry

/-- Exterior-power presheaf multiplication is natural in the module presheaf. -/
theorem mulHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) (n m : ℕ) :
    PresheafOfModules.Monoidal.tensorHom (hom 𝒪 f n) (hom 𝒪 f m) ≫
        mulHom 𝒪 G n m =
      mulHom 𝒪 F n m ≫ hom 𝒪 f (n + m) := sorry

/-- The objectwise degree-zero units commute with restriction maps. -/
theorem oneHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.unit (RingPresheaf 𝒪)).map i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorPower.one (sectionObj 𝒪 F V)) =
      ModuleCat.exteriorPower.one (sectionObj 𝒪 F U) ≫ map 𝒪 F 0 i := sorry

/-- The degree-zero unit morphism from the tensor-unit presheaf to `Λ⁰(F)`. -/
@[stacks 01CF "degree-zero unit of exterior-power presheaves"]
noncomputable def oneHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)) ⟶ presheaf 𝒪 F 0 where
  app U := ModuleCat.exteriorPower.one (sectionObj 𝒪 F U)
  naturality := oneHom_app_naturality 𝒪 F

/-- A component of the degree-zero unit is the corresponding `ModuleCat` unit. -/
theorem oneHom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (oneHom 𝒪 F).app U =
      ModuleCat.exteriorPower.one (sectionObj 𝒪 F U) := sorry

/-- The degree-zero unit sends the section-ring unit to the empty exterior product. -/
@[simp]
theorem oneHom_app_one
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (oneHom 𝒪 F).app U (1 : 𝒪.obj U) =
      ModuleCat.exteriorPower.mk (fun i : Fin 0 ↦ Fin.elim0 i) := sorry

/-- The degree-zero unit is natural in the module presheaf. -/
theorem oneHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    oneHom 𝒪 F ≫ hom 𝒪 f 0 = oneHom 𝒪 G := sorry

end PresheafOfModules.ExteriorPower

