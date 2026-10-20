/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap91.Lemma_91_14_2_FlatKernel
public import stacks_project.Chap76.Lemma_76_17_1_Difference
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

abbrev projection (L : FlatLift t f) :=
  (forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)

abbrev restrictedKernel (L : FlatLift t f) :=
  (restrictSpacesAdd X).obj (kernel (projection L))

/-- The actual first-order ideal inclusion, after the cartesian conormal comparison. -/
def inclusion (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf L.i)) :=
  (SheafOfModules.toSheaf (structureSheaf X)).map
      (cartesianConormalMap L ≫ pullbackQuotientToConormal L.i) ≫ conormalInclusion L.i

/-- The geometric first-order ideal inclusion lands in the kernel of the structure map. -/
theorem inclusion_comp_projection (L : FlatLift t f) :
    inclusion L ≫ (restrictSpacesAdd X).map (projection L) = 0 := sorry

/-- Restriction of sheaves to the small étale site preserves this kernel. -/
instance preservesProjectionKernel (L : FlatLift t f) :
    PreservesLimit (parallelPair (projection L) 0) (restrictSpacesAdd X) := by
  letI : PreservesLimit (parallelPair (projection L) 0)
      (restrictSpacesAdd X ⋙ sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u}) := by
    change PreservesLimit _
      (sheafToPresheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (smallEtaleToSpaces X).op)
    infer_instance
  exact preservesLimit_of_reflects_of_preserves (restrictSpacesAdd X)
    (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u})

/-- The kernel comparison is the universal lift of the concrete ideal inclusion. -/
def comparison (L : FlatLift t f) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f) ⟶
      restrictedKernel L :=
  kernel.lift ((restrictSpacesAdd X).map (projection L)) (inclusion L)
      (inclusion_comp_projection L) ≫
    (PreservesKernel.iso (restrictSpacesAdd X) (projection L)).inv

/-- The chosen kernel comparison recovers the fixed geometric ideal inclusion. -/
theorem comparison_fac (L : FlatLift t f) :
    comparison L ≫ (restrictSpacesAdd X).map (kernel.ι (projection L)) = inclusion L := by
  simp only [comparison, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- Reconstruct a section of the conormal from its actual kernel-comparison fiber.
The empty fiber is assigned zero, independently of any invertibility theorem. -/
def sectionPreimage (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U) :
    ((SheafOfModules.toSheaf (structureSheaf X)).obj (pulledConormal t f)).obj.obj U := by
  classical
  exact if h : ∃ x, (comparison L).hom.app U x = y then h.choose else 0

/-- Outside the actual kernel-comparison image the reconstruction is zero. -/
theorem sectionPreimage_of_not_mem (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U)
    (hy : ¬ ∃ x, (comparison L).hom.app U x = y) : sectionPreimage L U y = 0 := by
  classical
  simp only [sectionPreimage, dif_neg hy]

/-- The graph reconstruction maps back to every value in the actual image. -/
theorem comparison_sectionPreimage_of_mem (L : FlatLift t f)
    (U : (smallEtaleSite X)ᵒᵖ) (y : (restrictedKernel L).obj.obj U)
    (hy : ∃ x, (comparison L).hom.app U x = y) :
    (comparison L).hom.app U (sectionPreimage L U y) = y := sorry

/-- Reconstruction preserves the zero section of the canonical kernel. -/
theorem sectionPreimage_zero (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ) :
    sectionPreimage L U 0 = 0 := sorry

/-- Reconstruction is additive because the flat comparison identifies both actual modules. -/
theorem sectionPreimage_add (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
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

/-- The reverse kernel map evaluates by the actual graph reconstruction. -/
@[simp] theorem inverse_app (L : FlatLift t f) (U : (smallEtaleSite X)ᵒᵖ)
    (y : (restrictedKernel L).obj.obj U) :
    (inverse L).hom.app U y = sectionPreimage L U y := rfl

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

@[simp] theorem iso_hom (L : FlatLift t f) : (iso L).hom = inverse L := rfl

@[simp] theorem iso_inv (L : FlatLift t f) : (iso L).inv = comparison L := rfl
end AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.CanonicalKernel
