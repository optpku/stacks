/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.NaiveCotangent.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open scoped DerivedExt RingedSite.ToposHom
noncomputable section
universe u
namespace RingedSite.ToposHom

-- Local instance justification (defeq pin): the naive cotangent Ext maps use the standard module derived category of the extension classification.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf spelling must select that same standard localization.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

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

/-- A square-zero algebra extension of the source structure sheaf over the inverse-image base,
with its kernel identified with the specified module. -/
abbrev AlgebraExtension (F : ModuleCat.{u} (ofCommRingSheaf JC OC)) :=
  Solution (𝟙 (f.toTopos.commRingInverseImage.obj OB))
    (Solution.isSquareZero_id _)
    (commRingStructureMap f) F (zeroKernelMap (commRingStructureMap f) F)

namespace AlgebraExtension

variable {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
variable {G : ModuleCat.{u} (ofCommRingSheaf JD OD)}

/-- The class of an algebra extension is its canonical square-zero extension class. -/
def extClass (SC : AlgebraExtension f F) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj ((CochainComplex.singleFunctor _ 0).obj F)) :=
  Solution.extensionClass (commRingStructureMap f) F (Solution.isoClassMk SC)

/-- The kernel identification followed by the kernel inclusion is natural on underlying sheaves. -/
theorem kernelCarrierι_naturality (SC : AlgebraExtension f F)
    {U V : Cᵒᵖ} (h : U ⟶ V) :
    ((ToInternal.underlying (SheafOfModules.RingedSite.ringSheaf JC OC)).obj F).obj.map h ≫
        (↾fun x ↦ SheafOfModules.RingedSite.KernelIdeal.ιApp SC.proj V ((kernelIso_forget SC).hom.hom.app V x)) =
      (↾fun x ↦ SheafOfModules.RingedSite.KernelIdeal.ιApp SC.proj U ((kernelIso_forget SC).hom.hom.app U x)) ≫
        ((sheafCompose JC (forget CommRingCat.{u})).obj SC.middle).obj.map h := sorry

/-- The inclusion of the identified kernel into the middle algebra, on underlying sheaves. -/
def kernelCarrierι (SC : AlgebraExtension f F) :
    (ToInternal.underlying (SheafOfModules.RingedSite.ringSheaf JC OC)).obj F ⟶
      (sheafCompose JC (forget CommRingCat.{u})).obj SC.middle :=
  ⟨{ app := fun U ↦ ↾fun x ↦ SheafOfModules.RingedSite.KernelIdeal.ιApp SC.proj U ((kernelIso_forget SC).hom.hom.app U x)
     naturality := fun _ _ h ↦ kernelCarrierι_naturality f SC h }⟩

/-- The kernel inclusion sends a section to its image under the stored kernel identification. -/
theorem kernelCarrierι_apply (SC : AlgebraExtension f F) (U : Cᵒᵖ) (x : F.val.obj U) :
    (kernelCarrierι f SC).hom.app U x = SheafOfModules.RingedSite.KernelIdeal.ιApp SC.proj U ((kernelIso_forget SC).hom.hom.app U x) := sorry

/-- The coefficient carrier map is the scalar adjunct transported through geometric inverse image. -/
def coefficientCarrierMap (c : g.modulePullback.obj F ⟶ G) :
    g.toTopos.inverseImage.obj
      ((ToInternal.underlying (SheafOfModules.RingedSite.ringSheaf JC OC)).obj F) ⟶
        (ToInternal.underlying (SheafOfModules.RingedSite.ringSheaf JD OD)).obj G :=
  (g.toTopos.moduleInverseImageForgetIso
      (SheafOfModules.RingedSite.ringSheaf JC OC)).inv.app F ≫
    (ToInternal.underlying (g.toTopos.ringInverseImage.obj
      (SheafOfModules.RingedSite.ringSheaf JC OC))).map
        (ModulePullback.scalarHomEquiv g _ _ c)

/-- A map of middle algebras fits the two extensions when its quotient, base-algebra, and
identified-kernel maps agree with the specified geometric and coefficient maps. -/
def Fits (c : g.modulePullback.obj F ⟶ G)
    (SC : AlgebraExtension f F) (SD : AlgebraExtension (g.comp f) G)
    (φ : g.toTopos.commRingInverseImage.obj SC.middle ⟶ SD.middle) : Prop :=
  φ ≫ SD.proj = g.toTopos.commRingInverseImage.map SC.proj ≫ commRingStructureMap g ∧
    g.toTopos.commRingInverseImage.map SC.structureMap ≫ φ =
      (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv ≫
        SD.structureMap ∧
    g.toTopos.inverseImage.map (kernelCarrierι f SC) ≫
        (g.toTopos.commRingInverseImageForgetIso).inv.app SC.middle ≫
          (sheafCompose JD (forget CommRingCat.{u})).map φ =
      coefficientCarrierMap g c ≫ kernelCarrierι (g.comp f) SD

/-- Fitting is precisely the conjunction of quotient, base-algebra, and kernel compatibility. -/
theorem Fits.spec (c : g.modulePullback.obj F ⟶ G)
    (SC : AlgebraExtension f F) (SD : AlgebraExtension (g.comp f) G)
    (φ : g.toTopos.commRingInverseImage.obj SC.middle ⟶ SD.middle) :
    Fits f g c SC SD φ ↔
      φ ≫ SD.proj = g.toTopos.commRingInverseImage.map SC.proj ≫ commRingStructureMap g ∧
      g.toTopos.commRingInverseImage.map SC.structureMap ≫ φ =
        (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv ≫
          SD.structureMap ∧
      g.toTopos.inverseImage.map (kernelCarrierι f SC) ≫
          (g.toTopos.commRingInverseImageForgetIso).inv.app SC.middle ≫
            (sheafCompose JD (forget CommRingCat.{u})).map φ =
        coefficientCarrierMap g c ≫ kernelCarrierι (g.comp f) SD := sorry

/-- A compatible morphism of square-zero algebra extensions exists exactly when their
canonical classes have equal images in Ext from the derived inverse-image cotangent complex. -/
theorem fittingMap_exists_iff (c : g.modulePullback.obj F ⟶ G)
    (SC : AlgebraExtension f F) (SD : AlgebraExtension (g.comp f) G) :
    (∃ φ : g.toTopos.commRingInverseImage.obj SC.middle ⟶ SD.middle, Fits f g c SC SD φ) ↔
      NaiveCotangent.extOneMap f g c (extClass f SC) =
        NaiveCotangent.extOneComap f g (extClass (g.comp f) SD) := sorry

end AlgebraExtension
end RingedSite.ToposHom
