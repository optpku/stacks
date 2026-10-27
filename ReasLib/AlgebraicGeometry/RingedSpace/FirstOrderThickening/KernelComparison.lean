/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Conormal.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ScalarDescent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero

/-!
# Kernel comparisons for first-order thickenings

Inverse-image kernels and the pullback of the kernel ideal identify by transporting kernel
sections along the underlying homeomorphism. The inverse to the kernel adjunction unit is
specified by scalar descent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

/-- Inverse-image structure maps of thickenings are locally surjective. -/
instance instInverseImage_isLocallySurjective {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsThickening h] :
    Sheaf.IsLocallySurjective (inverseImageStructureSheafHomComm h) := sorry

/-- Inverse-image structure maps of first-order thickenings have square-zero kernels. -/
theorem inverseImage_isSquareZero {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    KernelIdeal.IsSquareZero (inverseImageStructureSheafHomComm h) := sorry

/-- The conormal sheaf maps to the inverse-image square-zero kernel module. -/
def conormalToTargetModule {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    conormalSheaf h ⟶
      (inverseImage_isSquareZero h).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (inverseImageStructureSheafHomComm h))) :=
  SheafOfModules.RingedSite.SquareZeroExtension.conormalToTarget
    (inverseImageStructureSheafHomComm h) (inverseImage_isSquareZero h)

/-- A first-order thickening induces an isomorphism of underlying topological spaces. -/
def thickeningBaseIso {X X' : RingedSpace.{u}} (h : X ⟶ X') [IsFirstOrderThickening h] :
    X.carrier ≅ X'.carrier :=
  @asIso TopCat.{u} _ X.carrier X'.carrier h.hom.base (instIsIso_base (i := h))

section Comparison

variable {X X' : RingedSpace.{u}} (h : X ⟶ X') [IsFirstOrderThickening h]

private abbrev targetKernel :=
  (inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h)))

private def homeoPullbackIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj X'.sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat.{u} (thickeningBaseIso h).inv).obj X'.sheaf :=
  (TopCat.Sheaf.pullbackIso CommRingCat.{u} h.hom.base).app X'.sheaf ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).mapIso
      ((TopCat.Presheaf.pullbackHomIsoPushforwardInv CommRingCat.{u}
        (thickeningBaseIso h)).app X'.presheaf) ≪≫
    (sheafificationIso (J := Opens.grothendieckTopology X)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} (thickeningBaseIso h).inv).obj X'.sheaf)).symm

private def forwardRaw (U : (Opens X')ᵒᵖ) (x : (kernelIdealSheaf h).val.obj U) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj X'.sheaf).obj.obj
      (op ((Opens.map h.hom.base).obj U.unop)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} h.hom.base).unit.app
    X'.sheaf).hom.app U (KernelIdeal.ιApp (commRingSheafPushforwardMap h) U x)

private def reverseRaw (U : (Opens X)ᵒᵖ) (x : (targetKernel h).val.obj U) :
    X'.presheaf.obj (op ((Opens.map (thickeningBaseIso h).inv).obj U.unop)) :=
  (homeoPullbackIso h).hom.hom.app U
    (KernelIdeal.ιApp (inverseImageStructureSheafHomComm h) U
      (((inverseImage_isSquareZero h).targetModuleForgetIso
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (inverseImageStructureSheafHomComm h)))).hom.hom.app U x))

private abbrev ForwardMembership :=
  ∀ U x, forwardRaw h U x ∈ KernelIdeal.sectionIdeal
    (inverseImageStructureSheafHomComm h) (op ((Opens.map h.hom.base).obj U.unop))

private abbrev ReverseMembership :=
  ∀ U x, reverseRaw h U x ∈ KernelIdeal.sectionIdeal (commRingSheafPushforwardMap h)
    (op ((Opens.map (thickeningBaseIso h).inv).obj U.unop))

set_option backward.isDefEq.respectTransparency false in
private def forwardAdd (hf : ForwardMembership h) (U : (Opens X')ᵒᵖ) :
    (kernelIdealSheaf h).val.obj U →+ (targetKernel h).val.obj
      (op ((Opens.map h.hom.base).obj U.unop)) :=
  (((inverseImage_isSquareZero h).targetModuleForgetIso
    (inferInstance : IsIso (KernelIdeal.quotientComparison
      (inverseImageStructureSheafHomComm h)))).inv.hom.app _).hom.comp
    (((KernelIdeal.sectionsIso (inverseImageStructureSheafHomComm h) _).inv.hom.toAddMonoidHom).comp
      { toFun := fun x ↦ ⟨forwardRaw h U x, hf U x⟩
        map_zero' := by apply Subtype.ext; simp [forwardRaw, KernelIdeal.ιApp]
        map_add' := by intro x y; apply Subtype.ext; simp [forwardRaw, KernelIdeal.ιApp] })

set_option backward.isDefEq.respectTransparency false in
private def reverseAdd (hr : ReverseMembership h) (U : (Opens X)ᵒᵖ) :
    (targetKernel h).val.obj U →+ (idealModule h).val.obj U :=
  ((idealModule h).val.map
    ((Opens.mapMapIso (thickeningBaseIso h)).counitIso.inv.app U.unop).op).hom.toAddMonoidHom.comp
    ((((pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h)).val.app
      (op ((Opens.map (thickeningBaseIso h).inv).obj U.unop))).hom.toAddMonoidHom.comp
      (((KernelIdeal.sectionsIso (commRingSheafPushforwardMap h)
        (op ((Opens.map (thickeningBaseIso h).inv).obj U.unop))).inv.hom.toAddMonoidHom).comp
        { toFun := fun x ↦ ⟨reverseRaw h U x, hr U x⟩
          map_zero' := by
            apply Subtype.ext
            change reverseRaw h U 0 = 0
            dsimp only [reverseRaw, KernelIdeal.ιApp]
            rw [map_zero, map_zero]
            exact map_zero ((homeoPullbackIso h).hom.hom.app U).hom
          map_add' := by
            intro x y
            apply Subtype.ext
            change reverseRaw h U (x + y) = reverseRaw h U x + reverseRaw h U y
            dsimp only [reverseRaw, KernelIdeal.ιApp]
            rw [map_add, map_add]
            exact map_add ((homeoPullbackIso h).hom.hom.app U).hom _ _ }))

private theorem kernelComparison_laws :
    ForwardMembership h ∧ ReverseMembership h ∧
    (∀ hf : ForwardMembership h,
      (∀ (U : (Opens X')ᵒᵖ) (r : X'.ringCatSheaf.obj.obj U)
        (x : (kernelIdealSheaf h).val.obj U),
        forwardAdd h hf U (r • x) =
          @SMul.smul (X.ringCatSheaf.obj.obj (op ((Opens.map h.hom.base).obj U.unop)))
            ((targetKernel h).val.obj (op ((Opens.map h.hom.base).obj U.unop))) inferInstance
            (h.hom.c.app U r) (forwardAdd h hf U x)) ∧
      (∀ {U V : (Opens X')ᵒᵖ} (i : U ⟶ V) (x : (kernelIdealSheaf h).val.obj U),
        forwardAdd h hf V ((kernelIdealSheaf h).val.map i x) =
          ((h _*).obj (targetKernel h)).val.map i (forwardAdd h hf U x))) ∧
    (∀ hr : ReverseMembership h,
      (∀ (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U)
        (x : (targetKernel h).val.obj U),
        reverseAdd h hr U (r • x) = r • reverseAdd h hr U x) ∧
      (∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : (targetKernel h).val.obj U),
        reverseAdd h hr V ((targetKernel h).val.map i x) =
          (idealModule h).val.map i (reverseAdd h hr U x))) := sorry

/-- The kernel ideal maps to the pushforward of its inverse-image square-zero kernel module. -/
@[no_expose] def kernelIdealToPushforwardTarget :
    kernelIdealSheaf h ⟶ (h _*).obj (((inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h))))) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (forwardAdd h (kernelComparison_laws h).1 U)
      naturality := by
        intro U V i
        ext x
        exact (kernelComparison_laws h).2.2.1 _ |>.2 i x }
    (fun U r x ↦ (kernelComparison_laws h).2.2.1 _ |>.1 U r x)

/-- Pullback of the kernel ideal maps to the inverse-image square-zero kernel module. -/
@[no_expose] def idealModuleToTargetModule : idealModule h ⟶ ((inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h)))) :=
  ((pullbackPushforwardAdjunction h).homEquiv _ _).symm (kernelIdealToPushforwardTarget h)

/-- Kernel sections transported through the underlying homeomorphism map to the pulled-back
kernel ideal by the module adjunction unit. -/
@[no_expose] def targetModuleToIdealModule : ((inverseImage_isSquareZero h).targetModule
    (inferInstance : IsIso (KernelIdeal.quotientComparison (inverseImageStructureSheafHomComm h)))) ⟶ idealModule h where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (reverseAdd h (kernelComparison_laws h).2.1 U)
      naturality := by
        intro U V i
        ext x
        exact (kernelComparison_laws h).2.2.2 _ |>.2 i x }
    (fun U r x ↦ (kernelComparison_laws h).2.2.2 _ |>.1 U r x)

/-- The two kernel comparisons are inverse. -/
theorem kernelComparison_inverse_laws :
    idealModuleToTargetModule h ≫ targetModuleToIdealModule h = 𝟙 _ ∧
      targetModuleToIdealModule h ≫ idealModuleToTargetModule h = 𝟙 _ := sorry

/-- The forward kernel comparison is an isomorphism with its specified reverse. -/
instance instIsIso_idealModuleToTargetModule : IsIso (idealModuleToTargetModule h) :=
  ⟨⟨targetModuleToIdealModule h, (kernelComparison_inverse_laws h).1,
    (kernelComparison_inverse_laws h).2⟩⟩

/-- The square-zero kernel ideal is annihilated by the structure-map kernel. -/
theorem kernelIdealPushforwardInv_laws :
    SheafOfModules.IsAnnihilatedByKernel (toRingCatSheafHom h) (kernelIdealSheaf h) := sorry

/-- The reverse to the kernel adjunction unit is specified by scalar descent and its counit. -/
def kernelIdealPushforwardInv : (h _*).obj (idealModule h) ⟶ kernelIdealSheaf h :=
  Hom.ScalarDescent.unitInv h (kernelIdealSheaf h) (kernelIdealPushforwardInv_laws h)

/-- The kernel adjunction unit and its scalar-descent reverse are inverse maps. -/
theorem kernelIdealPushforward_inverse_laws :
    (pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h) ≫
      kernelIdealPushforwardInv h = 𝟙 _ ∧
    kernelIdealPushforwardInv h ≫
      (pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h) = 𝟙 _ := sorry

/-- The kernel adjunction unit is invertible with the specified scalar-descent reverse. -/
instance instIsIso_unit_app_kernelIdeal :
    IsIso ((pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h)) :=
  ⟨⟨kernelIdealPushforwardInv h, (kernelIdealPushforward_inverse_laws h).1,
    (kernelIdealPushforward_inverse_laws h).2⟩⟩

/-- The kernel ideal identifies with the pushforward of its pullback module. -/
def kernelIdealPushforwardIso : kernelIdealSheaf h ≅ (h _*).obj (idealModule h) where
  hom := (pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h)
  inv := kernelIdealPushforwardInv h
  hom_inv_id := (kernelIdealPushforward_inverse_laws h).1
  inv_hom_id := (kernelIdealPushforward_inverse_laws h).2

/-- A first-order thickening is an epimorphism on the underlying additive structure sheaves. -/
instance instEpi_toSheaf_map_unitToPushforwardObjUnit :
    Epi ((SheafOfModules.toSheaf X'.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom h))) := sorry

end Comparison

/-- Underlying additive groups of module direct images are sections on inverse-image opens. -/
def pushforwardAppAddIso {X Y : RingedSpace.{u}} (h : X ⟶ Y) (N : X.Modules)
    (U : (Opens Y.carrier)ᵒᵖ) :
    (forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj U)) AddCommGrpCat.{u}).obj
        (((h _*).obj N).val.obj U) ≅
      (forget₂ (ModuleCat.{u}
          (X.ringCatSheaf.obj.obj (op ((Opens.map h.hom.base).obj (unop U)))))
        AddCommGrpCat.{u}).obj
        (N.val.obj (op ((Opens.map h.hom.base).obj (unop U)))) := Iso.refl _

/-- The underlying additive group of the unit module is the additive structure sheaf. -/
def unitAppAddIso {X : RingedSpace.{u}} (U : (Opens X.carrier)ᵒᵖ) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj U)) AddCommGrpCat.{u}).obj
        ((SheafOfModules.unit X.ringCatSheaf).val.obj U) ≅
      (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj
        ((forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.obj U)) := Iso.refl _

/-- An additive section of a module is its underlying module section. -/
def addToModuleSection {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (x : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) : M := x

end AlgebraicGeometry.RingedSpace.Thickening
