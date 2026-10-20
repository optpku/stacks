/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.DegreeZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeroth symmetric powers of module presheaves

The sectionwise zeroth symmetric-power isomorphisms assemble into a canonical
isomorphism with the tensor-unit presheaf.  The existing symmetric unit is
retained as the inverse component.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Objectwise zeroth symmetric-power isomorphisms commute with restriction maps. -/
theorem degreeZeroIso_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf 𝒪 F 0).map f ≫
        (ModuleCat.restrictScalars ((RingPresheaf 𝒪).map f).hom).map
          (ModuleCat.symmetricPower.iso₀ (sectionObj 𝒪 F V)).hom =
      (ModuleCat.symmetricPower.iso₀ (sectionObj 𝒪 F U)).hom ≫
        (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪))).map f := sorry

/-- A module presheaf is canonically isomorphic to its zeroth symmetric power. -/
@[stacks 01CF "zeroth symmetric power of module presheaves"]
noncomputable def degreeZeroIso
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    presheaf 𝒪 F 0 ≅ 𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)) :=
  PresheafOfModules.isoMk
    (fun U ↦ ModuleCat.symmetricPower.iso₀ (sectionObj 𝒪 F U))
    (fun _ _ f ↦ degreeZeroIso_app_naturality 𝒪 F f)

/-- The canonical projection from the zeroth symmetric-power presheaf to the tensor unit. -/
@[stacks 01CF "zeroth symmetric power presheaf projection"]
noncomputable def degreeZero
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    presheaf 𝒪 F 0 ⟶ 𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)) :=
  (degreeZeroIso 𝒪 F).hom

/-- The forward map of the degree-zero presheaf isomorphism is `degreeZero`. -/
@[simp]
theorem degreeZeroIso_hom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeZeroIso 𝒪 F).hom = degreeZero 𝒪 F := sorry

/-- The inverse degree-zero presheaf map is the existing symmetric unit. -/
@[simp]
theorem degreeZeroIso_inv
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeZeroIso 𝒪 F).inv = oneHom 𝒪 F := sorry

/-- The degree-zero symmetric unit is an isomorphism. -/
instance oneHom_isIso
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    IsIso (oneHom 𝒪 F) := sorry

/-- Zeroth symmetric-power projections are natural in the module presheaf. -/
@[reassoc]
theorem degreeZero_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    hom 𝒪 f 0 ≫ degreeZero 𝒪 G = degreeZero 𝒪 F := sorry

/-- Naturality of the zeroth symmetric-power identification. -/
theorem degreeZeroIso_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    (functor 𝒪 0).map f ≫ (degreeZeroIso 𝒪 G).hom =
      (degreeZeroIso 𝒪 F).hom ≫
        ((Functor.const _).obj
          (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)))).map f := sorry

/-- Naturality of the inverse zeroth symmetric-power identification. -/
theorem degreeZeroIso_inv_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    ((Functor.const _).obj
          (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪)))).map f ≫
        (degreeZeroIso 𝒪 G).inv =
      (degreeZeroIso 𝒪 F).inv ≫ (functor 𝒪 0).map f := sorry

/-- The degree-zero maps form the forward natural transformation to the tensor unit. -/
@[stacks 01CF "forward zeroth symmetric power natural transformation"]
noncomputable def degreeZeroNatTrans :
    functor 𝒪 0 ⟶
      (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪))) where
  app F := (degreeZeroIso 𝒪 F).hom
  naturality _ _ f := degreeZeroIso_naturality 𝒪 f

/-- The inverse degree-zero components form the reverse natural transformation. -/
@[stacks 01CF "inverse zeroth symmetric power natural transformation"]
noncomputable def degreeZeroInvNatTrans :
    (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪))) ⟶
      functor 𝒪 0 where
  app F := (degreeZeroIso 𝒪 F).inv
  naturality _ _ f := degreeZeroIso_inv_naturality 𝒪 f

/-- The forward degree-zero natural transformation followed by its inverse is the identity. -/
@[simp]
theorem degreeZeroNatTrans_hom_inv_id :
    degreeZeroNatTrans 𝒪 ≫ degreeZeroInvNatTrans 𝒪 = 𝟙 _ := sorry

/-- The inverse degree-zero natural transformation followed by the forward one is the identity. -/
@[simp]
theorem degreeZeroNatTrans_inv_hom_id :
    degreeZeroInvNatTrans 𝒪 ≫ degreeZeroNatTrans 𝒪 = 𝟙 _ := sorry

/-- Zeroth symmetric powers are naturally the tensor-unit presheaf. -/
@[stacks 01CF "natural zeroth symmetric power of module presheaves"]
noncomputable def degreeZeroNatIso :
    functor 𝒪 0 ≅
      (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf 𝒪))) :=
  { hom := degreeZeroNatTrans 𝒪
    inv := degreeZeroInvNatTrans 𝒪
    hom_inv_id := degreeZeroNatTrans_hom_inv_id 𝒪
    inv_hom_id := degreeZeroNatTrans_inv_hom_id 𝒪 }

/-- A component of `degreeZeroNatIso` is `degreeZeroIso`. -/
@[simp]
theorem degreeZeroNatIso_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeZeroNatIso 𝒪).app F = degreeZeroIso 𝒪 F := sorry

/-- The forward map of `degreeZeroNatIso` is explicit. -/
@[simp]
theorem degreeZeroNatIso_hom :
    (degreeZeroNatIso 𝒪).hom = degreeZeroNatTrans 𝒪 := sorry

/-- The inverse map of `degreeZeroNatIso` is explicit. -/
@[simp]
theorem degreeZeroNatIso_inv :
    (degreeZeroNatIso 𝒪).inv = degreeZeroInvNatTrans 𝒪 := sorry

/-- The forward component of `degreeZeroNatIso` is `degreeZero`. -/
@[simp]
theorem degreeZeroNatIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeZeroNatIso 𝒪).hom.app F = degreeZero 𝒪 F := sorry

/-- The inverse component of `degreeZeroNatIso` is the symmetric unit. -/
@[simp]
theorem degreeZeroNatIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    (degreeZeroNatIso 𝒪).inv.app F = (degreeZeroIso 𝒪 F).inv := sorry

end PresheafOfModules.SymmetricPower
