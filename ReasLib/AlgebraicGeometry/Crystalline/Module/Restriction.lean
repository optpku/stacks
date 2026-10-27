/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.StructureSheaf
public import ReasLib.AlgebraicGeometry.Crystalline.Module

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restriction to a thickening evaluates the crystalline module on its actual open restrictions. -/
def restrictObj
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : RelativeCRIS S I γ h_compatible X x₀) : A.1.thickening.Modules where
  val := (PresheafOfModules.pushforward (F := relativeOpensFunctor A)
    ({ app U := RingCat.ofHom
          ((Scheme.Opens.ι U.unop).appLE U.unop ⊤ (by intro x hx; exact x.property)).hom
       naturality := sorry } :
      A.1.thickening.ringCatSheaf.obj ⟶ (relativeOpensFunctor A).op ⋙ structureSheaf.obj)).obj F.val
  isSheaf := sorry

/-- The restriction comparison is adjoint to the maps on the actual inverse-image open restrictions. -/
def restrictComparison
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B) :
    (Scheme.Modules.pullback f.thickening).obj (restrictObj F B) ⟶
      restrictObj F A :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f.thickening).homEquiv _ _).symm
    { val :=
        { app U := ModuleCat.ofHom
            (X := (restrictObj F B).val.obj U)
            (Y := ((Scheme.Modules.pushforward f.thickening).obj (restrictObj F A)).val.obj U)
            { toFun := fun x => F.val.map
                  (Quiver.Hom.op (CrystallineObject.Hom.restrictOpen f U.unop :
                    relativeRestrictOpen A (f.thickening ⁻¹ᵁ U.unop) ⟶
                      relativeRestrictOpen B U.unop)) x
              map_add' := fun x y => map_add _ x y
              map_smul' := sorry }
          naturality := sorry } }

/-- Restriction comparisons agree with the canonical identity pullback. -/
theorem restrictComparison_id
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : RelativeCRIS S I γ h_compatible X x₀) :
    restrictComparison F (𝟙 A) =
      (Scheme.Modules.pullbackId A.1.thickening).hom.app (restrictObj F A) := sorry

/-- Restriction comparisons compose through the canonical pullback compositor. -/
theorem restrictComparison_comp
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B C : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B) (g : B ⟶ C) :
    restrictComparison F (f ≫ g) =
      (Scheme.Modules.pullbackComp f.thickening g.thickening).inv.app
          (restrictObj F C) ≫
        (Scheme.Modules.pullback f.thickening).map (restrictComparison F g) ≫
          restrictComparison F f := sorry

/-- A crystalline sheaf of modules determines a coherent family of modules on its thickenings. -/
def restrict
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    ModuleSheaf (RelativeCRIS S I γ h_compatible X x₀) (fun A => A.1.thickening) (fun {A B} (f : A ⟶ B) => f.thickening) where
  obj := restrictObj F
  comparison := restrictComparison F
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := fun A => (restrictComparison_id F A).trans (Category.id_comp _).symm
  comparison_comp := fun f g => (restrictComparison_comp F f g).trans (Category.id_comp _).symm

/-- Evaluation of a restricted coefficient is its actual thickening restriction. -/
theorem restrict_obj
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : RelativeCRIS S I γ h_compatible X x₀) :
    (restrict F).obj A = restrictObj F A := rfl

/-- The comparisons of the restricted family are induced by the original sheaf maps. -/
theorem restrict_comparison
    (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B : RelativeCRIS S I γ h_compatible X x₀} (f : A ⟶ B) :
    (restrict F).comparison f = restrictComparison F f := rfl

/-- Restriction to a thickening evaluates the crystalline module on its actual open restrictions. -/
def CrisModuleSheaf.restrictObj
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : smallCrystallineSite S I γ h_compatible X x₀) : A.obj.1.thickening.Modules where
  val := (PresheafOfModules.pushforward (F := smallOpensFunctor A)
    ({ app U := RingCat.ofHom
          ((Scheme.Opens.ι U.unop).appLE U.unop ⊤ (by intro x hx; exact x.property)).hom
       naturality := sorry } :
      A.obj.1.thickening.ringCatSheaf.obj ⟶ (smallOpensFunctor A).op ⋙ smallStructureSheaf.obj)).obj F.val
  isSheaf := sorry

/-- The restriction comparison is adjoint to the maps on the actual inverse-image open restrictions. -/
def CrisModuleSheaf.restrictComparison
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) :
    (Scheme.Modules.pullback f.hom.thickening).obj (CrisModuleSheaf.restrictObj F B) ⟶
      CrisModuleSheaf.restrictObj F A :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f.hom.thickening).homEquiv _ _).symm
    { val :=
        { app U := ModuleCat.ofHom
            (X := (CrisModuleSheaf.restrictObj F B).val.obj U)
            (Y := ((Scheme.Modules.pushforward f.hom.thickening).obj
              (CrisModuleSheaf.restrictObj F A)).val.obj U)
            { toFun := fun x => F.val.map
                  (ObjectProperty.homMk (CrystallineObject.Hom.restrictOpen f.hom U.unop)).op x
              map_add' := fun x y => map_add _ x y
              map_smul' := sorry }
          naturality := sorry } }

/-- Restriction comparisons agree with the canonical identity pullback. -/
theorem CrisModuleSheaf.restrictComparison_id
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    CrisModuleSheaf.restrictComparison F (𝟙 A) =
      (Scheme.Modules.pullbackId A.obj.1.thickening).hom.app (CrisModuleSheaf.restrictObj F A) := sorry

/-- Restriction comparisons compose through the canonical pullback compositor. -/
theorem CrisModuleSheaf.restrictComparison_comp
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B C : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) (g : B ⟶ C) :
    CrisModuleSheaf.restrictComparison F (f ≫ g) =
      (Scheme.Modules.pullbackComp f.hom.thickening g.hom.thickening).inv.app
          (CrisModuleSheaf.restrictObj F C) ≫
        (Scheme.Modules.pullback f.hom.thickening).map (CrisModuleSheaf.restrictComparison F g) ≫
          CrisModuleSheaf.restrictComparison F f := sorry

/-- A crystalline sheaf of modules determines a coherent family of modules on its thickenings. -/
def CrisModuleSheaf.restrict
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj := CrisModuleSheaf.restrictObj F
  comparison := CrisModuleSheaf.restrictComparison F
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := fun A => (CrisModuleSheaf.restrictComparison_id F A).trans (Category.id_comp _).symm
  comparison_comp := fun f g => (CrisModuleSheaf.restrictComparison_comp F f g).trans (Category.id_comp _).symm

/-- Evaluation of a restricted coefficient is its actual thickening restriction. -/
theorem CrisModuleSheaf.restrict_obj
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    (CrisModuleSheaf.restrict F).obj A = CrisModuleSheaf.restrictObj F A := rfl

/-- The comparisons of the restricted family are induced by the original sheaf maps. -/
theorem CrisModuleSheaf.restrict_comparison
    (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)))
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) :
    (CrisModuleSheaf.restrict F).comparison f = CrisModuleSheaf.restrictComparison F f := rfl

end CrystallineModuleSheaf
