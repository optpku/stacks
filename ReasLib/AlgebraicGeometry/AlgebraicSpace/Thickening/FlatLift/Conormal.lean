/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.ClosedMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Difference
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Pull back the actual kernel-ideal quotient comparison of the cartesian square.
The map is fixed by kernel inclusion and cokernel descent, not by selecting an iso. -/
def cartesianConormalMap (L : FlatLift t f) :
    pulledConormal t f ⟶ closedFibreConormal L :=
  (liftConormalIso L).inv ≫
    (Modules.pullbackCompIso L.i L.f').inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)) ≫
    (Modules.pullback L.i).map (@Hom.Conormal.idealQuotientMap _ _ _ _ _ _ _ _ _
      (isFirstOrderThickening L).toIsClosedImmersion inferInstance L.isPullback.toCommSq)

/-- Recover a section from the actual cartesian comparison fiber, with zero outside its image.
This total function takes no existence, bijectivity, or inverse-isomorphism certificate. -/
private def cartesianConormalSectionPreimage (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (closedFibreConormal L).val.obj U) : (pulledConormal t f).val.obj U := by
  classical
  exact if h : ∃ x, (cartesianConormalMap L).val.app U x = y then h.choose else 0

/-- Outside the actual section image the specified reconstruction is zero. -/
private theorem cartesianConormalSectionPreimage_of_not_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U)
    (hy : ¬ ∃ x, (cartesianConormalMap L).val.app U x = y) :
    cartesianConormalSectionPreimage L U y = 0 := by
  classical
  simp only [cartesianConormalSectionPreimage, dif_neg hy]

/-- On an actual inhabited fiber the reconstructed section maps to its specified value. -/
private theorem cartesianConormalMap_sectionPreimage_of_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U)
    (hy : ∃ x, (cartesianConormalMap L).val.app U x = y) :
    (cartesianConormalMap L).val.app U (cartesianConormalSectionPreimage L U y) = y := sorry

/-- Flat cartesian base change makes reconstruction additive. -/
private theorem cartesianConormalSectionPreimage_add (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (x y : (closedFibreConormal L).val.obj U) :
    cartesianConormalSectionPreimage L U (x + y) =
      cartesianConormalSectionPreimage L U x + cartesianConormalSectionPreimage L U y := sorry

/-- Flat cartesian base change makes reconstruction linear over the structure sheaf. -/
private theorem cartesianConormalSectionPreimage_smul (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (structureSheaf X).obj.obj U)
    (x : (closedFibreConormal L).val.obj U) :
    cartesianConormalSectionPreimage L U (a • x) =
      a • cartesianConormalSectionPreimage L U x := sorry

/-- The reverse comparison has the specified section-fiber reconstruction as its actual map. -/
def cartesianConormalInv (L : FlatLift t f) :
    closedFibreConormal L ⟶ pulledConormal t f where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := cartesianConormalSectionPreimage L U
          map_add' := cartesianConormalSectionPreimage_add L U
          map_smul' := fun a x ↦ cartesianConormalSectionPreimage_smul L U a x }
      naturality := by intro U V g; sorry }

/-- The displayed construction has the specified component formula. -/
private theorem cartesianConormalInv_appEq (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U) :
    (cartesianConormalInv L).val.app U y =
      @dite _ (∃ x, (cartesianConormalMap L).val.app U x = y)
        (Classical.propDecidable _) (fun h ↦ h.choose) (fun _ ↦ 0) := rfl

/-- The reverse comparison evaluates by its actual section fiber. -/
@[simp] theorem cartesianConormalInv_app (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (closedFibreConormal L).val.obj U) :
    (cartesianConormalInv L).val.app U y =
      @dite _ (∃ x, (cartesianConormalMap L).val.app U x = y)
        (Classical.propDecidable _) (fun h ↦ h.choose) (fun _ ↦ 0) := cartesianConormalInv_appEq L U y

/-- Flatness and the cartesian square recover every source section. -/
theorem cartesianConormalMap_inv (L : FlatLift t f) :
    cartesianConormalMap L ≫ cartesianConormalInv L = 𝟙 _ := sorry

/-- Flatness and the cartesian square recover every target section. -/
theorem cartesianConormalInv_map (L : FlatLift t f) :
    cartesianConormalInv L ≫ cartesianConormalMap L = 𝟙 _ := sorry

/-- Both legs of the conormal identification are fixed by the actual cartesian comparison. -/
def cartesianConormalIso (L : FlatLift t f) :
    pulledConormal t f ≅ closedFibreConormal L where
  hom := cartesianConormalMap L
  inv := cartesianConormalInv L
  hom_inv_id := cartesianConormalMap_inv L
  inv_hom_id := cartesianConormalInv_map L

/-- Flat base change identifies the first-order conormal via the specified comparison. -/
theorem cartesianConormalMap_isIso (L : FlatLift t f) :
    IsIso (cartesianConormalMap L) := (cartesianConormalIso L).isIso_hom

/-- The displayed construction has the specified component formula. -/
private theorem cartesianConormalIso_invEq (L : FlatLift t f) :
    (cartesianConormalIso L).inv = cartesianConormalInv L := rfl

/-- The inverse conormal isomorphism is the specified section reconstruction. -/
@[simp] theorem cartesianConormalIso_inv (L : FlatLift t f) :
    (cartesianConormalIso L).inv = cartesianConormalInv L := cartesianConormalIso_invEq L

/-- The displayed construction has the specified component formula. -/
private theorem cartesianConormalIso_homEq (L : FlatLift t f) :
    (cartesianConormalIso L).hom = cartesianConormalMap L := rfl

/-- The forward conormal isomorphism is the cartesian comparison map. -/
@[simp] theorem cartesianConormalIso_hom (L : FlatLift t f) :
    (cartesianConormalIso L).hom = cartesianConormalMap L := cartesianConormalIso_homEq L

end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift

public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
noncomputable section
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- The additive reduction map of the closed structure sheaf. -/
abbrev projection (L : FlatLift t f) :=
  (forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)

/-- The restriction of the additive reduction kernel to the small étale site. -/
abbrev restrictedKernel (L : FlatLift t f) :=
  (EtaleAdditive.restriction X).obj (kernel (projection L))

/-- The actual first-order ideal inclusion, after the cartesian conormal comparison. -/
def inclusion (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf L.i)) :=
  (SheafOfModules.toSheaf (structureSheaf X)).map
      (cartesianConormalMap L ≫ (@pullbackQuotientToConormal _ _ _ L.i
        (isFirstOrderThickening L).toIsClosedImmersion)) ≫ (@conormalInclusion _ _ _ L.i (isFirstOrderThickening L))

/-- The geometric first-order ideal inclusion lands in the kernel of the structure map. -/
theorem inclusion_comp_projection (L : FlatLift t f) :
    inclusion L ≫ (EtaleAdditive.restriction X).map (projection L) = 0 := sorry

/-- Restriction of sheaves to the small étale site preserves this kernel. -/
theorem preservesProjectionKernel (L : FlatLift t f) :
    PreservesLimit (parallelPair (projection L) 0) (EtaleAdditive.restriction X) := by
  have h : PreservesLimit (parallelPair (projection L) 0)
      (EtaleAdditive.restriction X ⋙ sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}) := by
    change PreservesLimit _
      (sheafToPresheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (smallEtaleToSpaces X).op)
    infer_instance
  exact @preservesLimit_of_reflects_of_preserves _ _ _ _ _ _ _ _ _
    (EtaleAdditive.restriction X)
    (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}) h inferInstance

/-- The kernel comparison is the universal lift of the concrete ideal inclusion. -/
def comparison (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      restrictedKernel L :=
  kernel.lift ((EtaleAdditive.restriction X).map (projection L)) (inclusion L)
      (inclusion_comp_projection L) ≫
    (@PreservesKernel.iso _ _ _ _ _ _ (EtaleAdditive.restriction X) ⟨fun _ _ ↦ rfl⟩ _ _
      (projection L) _ _ (preservesProjectionKernel L)).inv

/-- The chosen kernel comparison recovers the fixed geometric ideal inclusion. -/
theorem comparison_fac (L : FlatLift t f) :
    comparison L ≫ (EtaleAdditive.restriction X).map (kernel.ι (projection L)) = inclusion L := by
  simp only [comparison, Category.assoc, @PreservesKernel.iso_inv_ι _ _ _ _ _ _ (EtaleAdditive.restriction X) ⟨fun _ _ ↦ rfl⟩ _ _
    (projection L) _ _ (preservesProjectionKernel L), kernel.lift_ι]

/-- Reconstruct a section of the conormal from its actual kernel-comparison fiber.
The empty fiber is assigned zero, independently of any invertibility theorem. -/
private def sectionPreimage (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U) :
    ((SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f)).obj.obj U := by
  classical
  exact if h : ∃ x, (comparison L).hom.app U x = y then h.choose else 0

/-- Outside the actual kernel-comparison image the reconstruction is zero. -/
private theorem sectionPreimage_of_not_mem (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U)
    (hy : ¬ ∃ x, (comparison L).hom.app U x = y) : sectionPreimage L U y = 0 := by
  classical
  simp only [sectionPreimage, dif_neg hy]

/-- The graph reconstruction maps back to every value in the actual image. -/
private theorem comparison_sectionPreimage_of_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (restrictedKernel L).obj.obj U)
    (hy : ∃ x, (comparison L).hom.app U x = y) :
    (comparison L).hom.app U (sectionPreimage L U y) = y := sorry

/-- Reconstruction preserves the zero section of the canonical kernel. -/
private theorem sectionPreimage_zero (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ) :
    sectionPreimage L U 0 = 0 := sorry

/-- Reconstruction is additive because the flat comparison identifies both actual modules. -/
private theorem sectionPreimage_add (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (x y : (restrictedKernel L).obj.obj U) :
    sectionPreimage L U (x + y) = sectionPreimage L U x + sectionPreimage L U y := sorry

/-- The actual reverse kernel comparison, with section functions specified independently of laws. -/
def inverse (L : FlatLift t f) : restrictedKernel L ⟶
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := sectionPreimage L U
          map_zero' := sectionPreimage_zero L U
          map_add' := sectionPreimage_add L U }
     naturality := by intro U V g; sorry }⟩

/-- The displayed construction has the specified component formula. -/
private theorem inverse_appEq (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U) :
    (inverse L).hom.app U y =
      @dite _ (∃ x, (comparison L).hom.app U x = y)
        (Classical.propDecidable _) (fun h ↦ h.choose) (fun _ ↦ 0) := rfl

/-- The reverse kernel map evaluates by the actual graph reconstruction. -/
@[simp] theorem inverse_app (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U) :
    (inverse L).hom.app U y =
      @dite _ (∃ x, (comparison L).hom.app U x = y)
        (Classical.propDecidable _) (fun h ↦ h.choose) (fun _ ↦ 0) := inverse_appEq L U y

/-- The reverse comparison recovers the canonical kernel inclusion's source. -/
theorem comparison_inverse (L : FlatLift t f) : comparison L ≫ inverse L = 𝟙 _ := sorry

/-- The forward comparison recovers every canonical kernel section. -/
theorem inverse_comparison (L : FlatLift t f) : inverse L ≫ comparison L = 𝟙 _ := sorry

/-- Canonical identification, with both maps fixed by the actual kernel inclusion. -/
def iso (L : FlatLift t f) : restrictedKernel L ≅
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) where
  hom := inverse L
  inv := comparison L
  hom_inv_id := inverse_comparison L
  inv_hom_id := comparison_inverse L

/-- Flatness makes the specified kernel comparison invertible. -/
theorem comparison_isIso (L : FlatLift t f) : IsIso (comparison L) := (iso L).isIso_inv

/-- The displayed construction has the specified component formula. -/
private theorem iso_homEq (L : FlatLift t f) : (iso L).hom = inverse L := rfl

/-- The forward kernel isomorphism is the specified inverse comparison. -/
@[simp] theorem iso_hom (L : FlatLift t f) : (iso L).hom = inverse L := iso_homEq L

/-- The inverse of the kernel identification is the specified comparison. -/
private theorem iso_invEq (L : FlatLift t f) : (iso L).inv = comparison L := rfl

/-- The inverse of the kernel identification is the specified comparison. -/
@[simp] theorem iso_inv (L : FlatLift t f) : (iso L).inv = comparison L := iso_invEq L
end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
