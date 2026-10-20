/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of symmetric-power presheaves

The fixed-degree symmetric products on section modules commute with restriction and assemble into
presheaf morphisms
`presheaf 𝒪 F n ⊗ presheaf 𝒪 F m ⟶ presheaf 𝒪 F (n + m)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Objectwise symmetric products commute with restriction maps. -/
theorem mulHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj
        (presheaf 𝒪 F n) (presheaf 𝒪 F m)).map i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.symmetricPower.mul (sectionObj 𝒪 F V) n m) =
      ModuleCat.symmetricPower.mul (sectionObj 𝒪 F U) n m ≫
        map 𝒪 F (n + m) i := sorry

/-- The multiplication morphism
`presheaf 𝒪 F n ⊗ presheaf 𝒪 F m ⟶ presheaf 𝒪 F (n + m)` for a module presheaf. -/
@[stacks 01CF "multiplication of symmetric-power presheaves"]
noncomputable def mulHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) :
    PresheafOfModules.Monoidal.tensorObj
        (presheaf 𝒪 F n) (presheaf 𝒪 F m) ⟶
      presheaf 𝒪 F (n + m) where
  app U := ModuleCat.symmetricPower.mul (sectionObj 𝒪 F U) n m
  naturality := mulHom_app_naturality 𝒪 F n m

/-- A component of symmetric-power presheaf multiplication is the corresponding
`ModuleCat` multiplication. -/
theorem mulHom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) (U : Cᵒᵖ) :
    (mulHom 𝒪 F n m).app U =
      ModuleCat.symmetricPower.mul (sectionObj 𝒪 F U) n m := sorry

/-- Presheaf symmetric multiplication concatenates pure symmetric tensors sectionwise. -/
@[simp]
theorem mulHom_app_tmul_mk
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) (U : Cᵒᵖ)
    (x : SymmetricPower.UFin n → sectionObj 𝒪 F U)
    (y : SymmetricPower.UFin m → sectionObj 𝒪 F U) :
    (mulHom 𝒪 F n m).app U
        (ModuleCat.symmetricPower.mk x ⊗ₜ ModuleCat.symmetricPower.mk y) =
      ModuleCat.symmetricPower.mk (ModuleCat.symmetricPower.append x y) := sorry

/-- Symmetric-power presheaf multiplication is natural in the module presheaf. -/
theorem mulHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (n m : ℕ) :
    PresheafOfModules.Monoidal.tensorHom (hom 𝒪 f n) (hom 𝒪 f m) ≫
        mulHom 𝒪 G n m =
      mulHom 𝒪 F n m ≫ hom 𝒪 f (n + m) := sorry

/-- Objectwise degree-zero symmetric units commute with restriction maps. -/
theorem oneHom_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.unit (RingPresheaf 𝒪)).map i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.symmetricPower.one (sectionObj 𝒪 F V)) =
      ModuleCat.symmetricPower.one (sectionObj 𝒪 F U) ≫ map 𝒪 F 0 i := sorry

/-- The degree-zero unit morphism from the tensor-unit presheaf to `presheaf 𝒪 F 0`. -/
@[stacks 01CF "degree-zero unit of symmetric-power presheaves"]
noncomputable def oneHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)) ⟶ presheaf 𝒪 F 0 where
  app U := ModuleCat.symmetricPower.one (sectionObj 𝒪 F U)
  naturality := oneHom_app_naturality 𝒪 F

/-- A component of the degree-zero unit is the corresponding `ModuleCat` unit. -/
theorem oneHom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (oneHom 𝒪 F).app U =
      ModuleCat.symmetricPower.one (sectionObj 𝒪 F U) := sorry

/-- The degree-zero unit sends the section-ring unit to the empty pure symmetric tensor. -/
@[simp]
theorem oneHom_app_one
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (oneHom 𝒪 F).app U (1 : 𝒪.obj U) =
      ModuleCat.symmetricPower.mk (R := 𝒪.obj U) (M := sectionObj 𝒪 F U)
        (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down) := sorry

/-- The degree-zero symmetric unit is natural in the module presheaf. -/
theorem oneHom_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    oneHom 𝒪 F ≫ hom 𝒪 f 0 = oneHom 𝒪 G := sorry

/-- Symmetric-power presheaf multiplication is associative, with degree reindexing explicit. -/
theorem mulHom_assoc
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m k : ℕ) :
    (α_ (presheaf 𝒪 F n) (presheaf 𝒪 F m) (presheaf 𝒪 F k)).hom ≫
        (presheaf 𝒪 F n ◁ mulHom 𝒪 F m k) ≫ mulHom 𝒪 F n (m + k) =
      (mulHom 𝒪 F n m ▷ presheaf 𝒪 F k) ≫ mulHom 𝒪 F (n + m) k ≫
        eqToHom (congrArg (presheaf 𝒪 F) (Nat.add_assoc n m k)) := sorry

/-- The degree-zero symmetric presheaf is a left unit. -/
theorem oneHom_mul
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n : ℕ) :
    (λ_ (presheaf 𝒪 F n)).hom =
      (oneHom 𝒪 F ▷ presheaf 𝒪 F n) ≫ mulHom 𝒪 F 0 n ≫
        eqToHom (congrArg (presheaf 𝒪 F) (Nat.zero_add n)) := sorry

/-- The degree-zero symmetric presheaf is a right unit. -/
theorem mulHom_one
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n : ℕ) :
    (ρ_ (presheaf 𝒪 F n)).hom =
      (presheaf 𝒪 F n ◁ oneHom 𝒪 F) ≫ mulHom 𝒪 F n 0 ≫
        eqToHom (congrArg (presheaf 𝒪 F) (Nat.add_zero n)) := sorry

/-- Symmetric-power presheaf multiplication commutes with the symmetric braiding. -/
theorem mulHom_braiding
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (n m : ℕ) :
    (β_ (presheaf 𝒪 F n) (presheaf 𝒪 F m)).hom ≫ mulHom 𝒪 F m n =
      mulHom 𝒪 F n m ≫
        eqToHom (congrArg (presheaf 𝒪 F) (Nat.add_comm n m)) := sorry

end PresheafOfModules.SymmetricPower
