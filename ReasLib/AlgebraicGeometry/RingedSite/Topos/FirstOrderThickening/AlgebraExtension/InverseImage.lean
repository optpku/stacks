/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-! # Geometric inverse image of square-zero algebra extensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution

noncomputable section
set_option backward.privateInPublic true
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500

universe u
namespace RingedSite.ToposHom.AlgebraExtension

variable {B : Type u} [Category.{u} B] {JB : GrothendieckTopology B}
variable [JB.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JB.HasSheafCompose (forget RingCat.{u})]
variable [JB.HasSheafCompose (forget CommRingCat.{u})]
variable [JB.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JB CommRingCat.{u}] [JB.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JB AddCommGrpCat.{u}] [JB.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OB : Sheaf JB CommRingCat.{u}}
variable {C : Type u} [Category.{u} C] {JC : GrothendieckTopology C}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}] [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}] [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}}
variable {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget CommRingCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JD CommRingCat.{u}] [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}] [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OD : Sheaf JD CommRingCat.{u}}
variable (f : ToposHom (ofCommRingSheaf JC OC) (ofCommRingSheaf JB OB))
variable (g : ToposHom (ofCommRingSheaf JD OD) (ofCommRingSheaf JC OC))
variable [(SheafOfModules.restrictScalars.{u} g.structureMap).IsRightAdjoint]

variable {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
variable {G : ModuleCat.{u} (ofCommRingSheaf JD OD)}

/-- Geometric inverse-image coefficients transported to the commutative inverse-image ring. -/
def inverseImageCoeff (F : ModuleCat.{u} (ofCommRingSheaf JC OC)) :
    SheafOfModules (ringSheaf JD (g.toTopos.commRingInverseImage.obj OC)) :=
  (SheafOfModules.restrictScalars
    (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC)).obj
      ((g.toTopos.moduleInverseImage (ringSheaf JC OC)).obj F)

/-- The inverse-image kernel inclusion transported to the pulled middle ring. -/
private def inverseImageInclusion (S : AlgebraExtension f F) :
    (ToInternal.underlying (ringSheaf JD (g.toTopos.commRingInverseImage.obj OC))).obj
        (inverseImageCoeff g F) ⟶
      (sheafCompose JD (forget CommRingCat.{u})).obj
        (g.toTopos.commRingInverseImage.obj S.middle) :=
  (g.toTopos.moduleInverseImageForgetIso (ringSheaf JC OC)).hom.app F ≫
    g.toTopos.inverseImage.map (kernelCarrierι f S) ≫
      g.toTopos.commRingInverseImageForgetIso.inv.app S.middle

/-- A section of the transported inverse-image coefficient module lifted to the quotient kernel. -/
private def kernelComparisonApp (S : AlgebraExtension f F)
    (hs : KernelIdeal.IsSquareZero (g.toTopos.commRingInverseImage.map S.proj))
    (hi : IsIso (KernelIdeal.quotientComparison (g.toTopos.commRingInverseImage.map S.proj)))
    (hm : ∀ U x, (inverseImageInclusion f g S).hom.app U x ∈
      KernelIdeal.sectionIdeal (g.toTopos.commRingInverseImage.map S.proj) U)
    (U : Dᵒᵖ) (x : (inverseImageCoeff g F).val.obj U) :
    (hs.targetModule hi).val.obj U :=
  (hs.targetModuleForgetIso hi).inv.hom.app U
    ((KernelIdeal.sectionsIso (g.toTopos.commRingInverseImage.map S.proj) U).inv
      ⟨(inverseImageInclusion f g S).hom.app U x, hm U x⟩)

/-- Geometric inverse image preserves square-zero local surjections, and its canonical
kernel inclusion is additive, natural, and linear over the inverse-image quotient. -/
private theorem kernelComparison_laws (S : AlgebraExtension f F) :
    Sheaf.IsLocallySurjective (g.toTopos.commRingInverseImage.map S.proj) ∧
    KernelIdeal.IsSquareZero (g.toTopos.commRingInverseImage.map S.proj) ∧
    (∀ U x, (inverseImageInclusion f g S).hom.app U x ∈
      KernelIdeal.sectionIdeal (g.toTopos.commRingInverseImage.map S.proj) U) ∧
    (∀ hs hi hm,
      (∀ U x y, kernelComparisonApp f g S hs hi hm U (x + y) =
        kernelComparisonApp f g S hs hi hm U x + kernelComparisonApp f g S hs hi hm U y) ∧
      (∀ U V (h : U ⟶ V) x,
        (hs.targetModule hi).val.map h (kernelComparisonApp f g S hs hi hm U x) =
          kernelComparisonApp f g S hs hi hm V ((inverseImageCoeff g F).val.map h x)) ∧
      (∀ U (r : (g.toTopos.commRingInverseImage.obj OC).obj.obj U) x,
        kernelComparisonApp f g S hs hi hm U (r • x) =
          r • kernelComparisonApp f g S hs hi hm U x)) := sorry

/-- The quotient comparison of the pulled extension is invertible. -/
private def inverseImageQuotientIsIso (S : AlgebraExtension f F) :
    IsIso (KernelIdeal.quotientComparison (g.toTopos.commRingInverseImage.map S.proj)) :=
  @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
    (g.toTopos.commRingInverseImage.map S.proj) _ (kernelComparison_laws f g S).1

/-- The canonical morphism from pulled coefficients to the kernel of the pulled extension. -/
private def kernelComparison (S : AlgebraExtension f F) :
    inverseImageCoeff g F ⟶
      (kernelComparison_laws f g S).2.1.targetModule (inverseImageQuotientIsIso f g S) where
  val := PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (kernelComparisonApp f g S _ _ (kernelComparison_laws f g S).2.2.1 U)
        (((kernelComparison_laws f g S).2.2.2 _ _ _).1 U))
      naturality := fun U V h ↦ ConcreteCategory.hom_ext _ _
        (fun x ↦ (((kernelComparison_laws f g S).2.2.2 _ _ _).2.1 U V h x).symm) }
    ((kernelComparison_laws f g S).2.2.2 _ _ _).2.2

/-- Geometric inverse image identifies the full coefficient kernel. -/
private theorem kernelComparison_isIso (S : AlgebraExtension f F) :
    IsIso (kernelComparison f g S) := sorry

/-- The canonical identification of the pulled kernel with pulled coefficients. -/
private def inverseImageKernelIso (S : AlgebraExtension f F) :
    (kernelComparison_laws f g S).2.1.targetModule (inverseImageQuotientIsIso f g S) ≅
      inverseImageCoeff g F :=
  (@asIso _ _ _ _ (kernelComparison f g S) (kernelComparison_isIso f g S)).symm

/-- Inverse image preserves the base-algebra square and the zero map from the base kernel. -/
private theorem inverseImage_laws (S : AlgebraExtension f F) :
    (g.toTopos.commRingInverseImage.map S.structureMap ≫
        g.toTopos.commRingInverseImage.map S.proj =
      𝟙 _ ≫ g.toTopos.commRingInverseImage.map (commRingStructureMap f)) ∧
    (∀ h,
      kernelMapOf (𝟙 _) (isSquareZero_id _)
          (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
          (g.toTopos.commRingInverseImage.map S.proj)
          (kernelComparison_laws f g S).2.1 (inverseImageQuotientIsIso f g S)
          (g.toTopos.commRingInverseImage.map S.structureMap) h ≫
        (restrictionAlong (g.toTopos.commRingInverseImage.map (commRingStructureMap f))).map
          (inverseImageKernelIso f g S).hom =
      zeroKernelMap (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        (inverseImageCoeff g F)) := sorry

/-- Geometric inverse image of a square-zero algebra extension over its inverse-image base. -/
def inverseImage (S : AlgebraExtension f F) :
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _) (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      (inverseImageCoeff g F)
      (zeroKernelMap (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        (inverseImageCoeff g F)) where
  middle := g.toTopos.commRingInverseImage.obj S.middle
  proj := g.toTopos.commRingInverseImage.map S.proj
  structureMap := g.toTopos.commRingInverseImage.map S.structureMap
  proj_locallySurjective := (kernelComparison_laws f g S).1
  proj_squareZero := (kernelComparison_laws f g S).2.1
  proj_quotient_isIso := inverseImageQuotientIsIso f g S
  commutes := (inverseImage_laws f g S).1
  kernelIso := inverseImageKernelIso f g S
  induces_c := (inverseImage_laws f g S).2 _

/-- Inverse image uses the actual pulled ring and projection, and its identified kernel
inclusion is the geometric inverse image of the original identified kernel inclusion. -/
theorem inverseImage_spec (S : AlgebraExtension f F) :
    (inverseImage f g S).middle = g.toTopos.commRingInverseImage.obj S.middle ∧
    (inverseImage f g S).proj = g.toTopos.commRingInverseImage.map S.proj ∧
    (∀ U x, KernelIdeal.ιApp (inverseImage f g S).proj U
      ((kernelIso_forget (inverseImage f g S)).hom.hom.app U x) =
        (inverseImageInclusion f g S).hom.app U x) := sorry

/-- The base map of a composite extension expressed over successive inverse-image rings. -/
private def normalizedBaseMap (S : AlgebraExtension (g.comp f) G) :
    g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB) ⟶ S.middle :=
  (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv ≫ S.structureMap

/-- Normalizing the composite base preserves the quotient square and zero base-kernel map. -/
private theorem normalizeComposite_laws (S : AlgebraExtension (g.comp f) G) :
    (normalizedBaseMap f g S ≫ S.proj =
      𝟙 _ ≫ (g.toTopos.commRingInverseImage.map (commRingStructureMap f) ≫
        commRingStructureMap g)) ∧
    (∀ h, kernelMapOf (𝟙 _) (isSquareZero_id _)
        (g.toTopos.commRingInverseImage.map (commRingStructureMap f) ≫ commRingStructureMap g)
        S.proj S.proj_squareZero S.proj_quotient_isIso (normalizedBaseMap f g S) h ≫
      (restrictionAlong
        (g.toTopos.commRingInverseImage.map (commRingStructureMap f) ≫ commRingStructureMap g)).map
        S.kernelIso.hom = zeroKernelMap _ G) := sorry

/-- An extension of the composite morphism normalized to the successive inverse-image base. -/
def normalizeComposite (S : AlgebraExtension (g.comp f) G) :
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _)
      (g.toTopos.commRingInverseImage.map (commRingStructureMap f) ≫ commRingStructureMap g)
      G (zeroKernelMap _ G) where
  middle := S.middle
  proj := S.proj
  structureMap := normalizedBaseMap f g S
  proj_locallySurjective := S.proj_locallySurjective
  proj_squareZero := S.proj_squareZero
  proj_quotient_isIso := S.proj_quotient_isIso
  commutes := (normalizeComposite_laws f g S).1
  kernelIso := S.kernelIso
  induces_c := (normalizeComposite_laws f g S).2 _

/-- Composite-base normalization keeps the middle ring, projection, and coefficient identification,
and changes the base map by the inverse-image-composition isomorphism. -/
theorem normalizeComposite_spec (S : AlgebraExtension (g.comp f) G) :
    (normalizeComposite f g S).middle = S.middle ∧
    (normalizeComposite f g S).proj = S.proj ∧
    (normalizeComposite f g S).structureMap =
      (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv ≫ S.structureMap := sorry

end RingedSite.ToposHom.AlgebraExtension
