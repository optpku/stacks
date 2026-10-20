/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Multiplication

/-!
# Zeroth exterior powers of module presheaves

Mathlib's canonical isomorphism `ModuleCat.exteriorPower.iso₀` is compatible with restriction of
scalars and therefore assembles into an isomorphism from the zeroth exterior-power presheaf to the
tensor-unit presheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorPower

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The objectwise zeroth-exterior-power isomorphisms commute with restriction maps. -/
theorem degreeZeroIso_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf O F 0).map f ≫
        (ModuleCat.restrictScalars ((RingPresheaf O).map f).hom).map
          (ModuleCat.exteriorPower.iso₀ (sectionObj O F V)).hom =
      (ModuleCat.exteriorPower.iso₀ (sectionObj O F U)).hom ≫
        (𝟙_ (PresheafOfModules.{w} (RingPresheaf O))).map f := sorry

/-- The zeroth exterior-power presheaf is canonically the tensor-unit presheaf. -/
@[stacks 01CF "zeroth exterior power of module presheaves"]
noncomputable def degreeZeroIso
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    presheaf O F 0 ≅ 𝟙_ (PresheafOfModules.{w} (RingPresheaf O)) :=
  PresheafOfModules.isoMk
    (fun U ↦ ModuleCat.exteriorPower.iso₀ (sectionObj O F U))
    (fun _ _ f ↦ degreeZeroIso_app_naturality O F f)

/-- The canonical projection from the zeroth exterior-power presheaf to the tensor unit. -/
noncomputable def degreeZero
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    presheaf O F 0 ⟶ 𝟙_ (PresheafOfModules.{w} (RingPresheaf O)) :=
  (degreeZeroIso O F).hom

/-- The forward map of the zeroth-exterior-power isomorphism is `degreeZero`. -/
@[simp, stacks 01CF "zeroth exterior power forward map"]
theorem degreeZeroIso_hom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroIso O F).hom = degreeZero O F := sorry

/-- The inverse zeroth-exterior-power isomorphism is the exterior unit. -/
@[simp, stacks 01CF "zeroth exterior power inverse map"]
theorem degreeZeroIso_inv
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroIso O F).inv = oneHom O F := sorry

/-- The degree-zero exterior unit is canonically an isomorphism. -/
instance oneHom_isIso
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    IsIso (oneHom O F) := sorry

/-- Zeroth exterior-power projections are natural in the module presheaf. -/
@[reassoc]
theorem degreeZero_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    hom O f 0 ≫ degreeZero O G = degreeZero O F := sorry

/-- Naturality of the zeroth-exterior-power identification. -/
@[stacks 01CF "zeroth exterior power identification naturality"]
theorem degreeZeroIso_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    (functor O 0).map f ≫ (degreeZeroIso O G).hom =
      (degreeZeroIso O F).hom ≫
        ((Functor.const _).obj
          (𝟙_ (PresheafOfModules.{w} (RingPresheaf O)))).map f := sorry

/-- Naturality of the inverse zeroth-exterior-power identification. -/
@[stacks 01CF "inverse zeroth exterior power identification naturality"]
theorem degreeZeroIso_inv_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    ((Functor.const _).obj
          (𝟙_ (PresheafOfModules.{w} (RingPresheaf O)))).map f ≫
        (degreeZeroIso O G).inv =
      (degreeZeroIso O F).inv ≫ (functor O 0).map f := sorry

/-- The degree-zero exterior-power maps form the forward natural transformation to the tensor
unit. -/
@[stacks 01CF "forward zeroth exterior power natural transformation"]
noncomputable def degreeZeroNatTrans :
    functor O 0 ⟶
      (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf O))) where
  app F := (degreeZeroIso O F).hom
  naturality _ _ f := degreeZeroIso_naturality O f

/-- The inverse components of the degree-zero exterior-power identifications form the inverse
natural transformation. -/
@[stacks 01CF "inverse zeroth exterior power natural transformation"]
noncomputable def degreeZeroInvNatTrans :
    (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf O))) ⟶
      functor O 0 where
  app F := (degreeZeroIso O F).inv
  naturality _ _ f := degreeZeroIso_inv_naturality O f

/-- A component of the forward degree-zero natural transformation is `degreeZero`. -/
@[simp, stacks 01CF "forward zeroth exterior power natural transformation component"]
theorem degreeZeroNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroNatTrans O).app F = degreeZero O F := sorry

/-- A component of the inverse degree-zero natural transformation is the exterior unit. -/
@[simp, stacks 01CF "inverse zeroth exterior power natural transformation component"]
theorem degreeZeroInvNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroInvNatTrans O).app F = (degreeZeroIso O F).inv := sorry

/-- The forward degree-zero natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "zeroth exterior power natural transformation forward-inverse law"]
theorem degreeZeroNatTrans_hom_inv_id :
    degreeZeroNatTrans O ≫ degreeZeroInvNatTrans O = 𝟙 _ := sorry

/-- The inverse degree-zero natural transformation followed by its forward map is the identity. -/
@[simp, stacks 01CF "zeroth exterior power natural transformation inverse-forward law"]
theorem degreeZeroNatTrans_inv_hom_id :
    degreeZeroInvNatTrans O ≫ degreeZeroNatTrans O = 𝟙 _ := sorry

/-- Zeroth exterior powers are naturally the constant tensor-unit presheaf. -/
@[stacks 01CF "natural zeroth exterior power of module presheaves"]
noncomputable def degreeZeroNatIso :
    functor O 0 ≅
      (Functor.const _).obj (𝟙_ (PresheafOfModules.{w} (RingPresheaf O))) :=
  { hom := degreeZeroNatTrans O
    inv := degreeZeroInvNatTrans O
    hom_inv_id := degreeZeroNatTrans_hom_inv_id O
    inv_hom_id := degreeZeroNatTrans_inv_hom_id O }

/-- The forward natural transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism hom"]
theorem degreeZeroNatIso_hom :
    (degreeZeroNatIso O).hom = degreeZeroNatTrans O := sorry

/-- The inverse natural transformation of `degreeZeroNatIso` is explicit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism inverse"]
theorem degreeZeroNatIso_inv :
    (degreeZeroNatIso O).inv = degreeZeroInvNatTrans O := sorry

/-- A component of `degreeZeroNatIso` is the objectwise zeroth-exterior-power isomorphism. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism component"]
theorem degreeZeroNatIso_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroNatIso O).app F = degreeZeroIso O F := sorry

/-- The forward component of `degreeZeroNatIso` is `degreeZero`. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism hom component"]
theorem degreeZeroNatIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroNatIso O).hom.app F = degreeZero O F := sorry

/-- The inverse component of `degreeZeroNatIso` is the exterior unit. -/
@[simp, stacks 01CF "zeroth exterior power natural isomorphism inverse component"]
theorem degreeZeroNatIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (degreeZeroNatIso O).inv.app F = (degreeZeroIso O F).inv := sorry

end PresheafOfModules.ExteriorPower

