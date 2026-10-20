module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FlatMorphismSquare
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FlatComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.ModuleObstruction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor

/-! # Naturality of flat-module existence obstructions on ringed topoi -/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uB vB uC1 vC1 uC2 vC2 uB1 vB1 uB2 vB2 wExt

namespace RingedSite.ToposHom.Thickening

variable {C : Type uC} [Category.{vC} C]
variable {B : Type uB} [Category.{vB} B]
variable {C1 : Type uC1} [Category.{vC1} C1]
variable {C2 : Type uC2} [Category.{vC2} C2]
variable {B1 : Type uB1} [Category.{vB1} B1]
variable {B2 : Type uB2} [Category.{vB2} B2]
variable {JC : GrothendieckTopology C}
variable {JB : GrothendieckTopology B}
variable {JC1 : GrothendieckTopology C1}
variable {JC2 : GrothendieckTopology C2}
variable {JB1 : GrothendieckTopology B1}
variable {JB2 : GrothendieckTopology B2}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [HasSheafify JC1 AddCommGrpCat.{max uC vC}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JC2 AddCommGrpCat.{max uC vC}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JB1 AddCommGrpCat.{max uC vC}]
variable [JB1.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JB2 AddCommGrpCat.{max uC vC}]
variable [JB2.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasWeakSheafify JC AddCommGrpCat.{max uC vC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable {O : Sheaf JC CommRingCat.{max uC vC}}
variable {O_B : Sheaf JB CommRingCat.{max uC vC}}
variable {O1' : Sheaf JC1 CommRingCat.{max uC vC}}
variable {O2' : Sheaf JC2 CommRingCat.{max uC vC}}
variable {OB1' : Sheaf JB1 CommRingCat.{max uC vC}}
variable {OB2' : Sheaf JB2 CommRingCat.{max uC vC}}


namespace FlatMorphismSquare

variable {f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B)}
variable {i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC1 O1')}
variable {i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC2 O2')}
variable {t1 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB1 OB1')}
variable {t2 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB2 OB2')}
variable {f1' : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JB1 OB1')}
variable {f2' : ToposHom (ofCommRingSheaf JC2 O2') (ofCommRingSheaf JB2 OB2')}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening t1] [IsFirstOrderThickening t2]
variable [(SheafOfModules.restrictScalars.{max uC vC} f1'.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} f2'.structureMap).IsRightAdjoint]


variable [(SheafOfModules.restrictScalars.{max uC vC} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} i1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} i2.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} t1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} t2.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (i1.comp f1').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (i2.comp f2').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (f.comp t1).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (f.comp t2).structureMap).IsRightAdjoint]
variable (S : FlatMorphismSquare f i1 i2 t1 t2 f1' f2')

/-- The first restriction square induces its canonical comparison on source ideals. -/
def idealMap_fst : f.modulePullback.obj (idealModule t1) ⟶ idealModule i1 :=
  sourceIdealMap { upper := i1, left := f, right := f1', lower := t1, cell := S.comm1 }

/-- The second restriction square induces its canonical comparison on source ideals. -/
def idealMap_snd : f.modulePullback.obj (idealModule t2) ⟶ idealModule i2 :=
  sourceIdealMap { upper := i2, left := f, right := f2', lower := t2, cell := S.comm2 }

/-- Strictness and flatness identify the first pulled-back base ideal with the source ideal. -/
def idealIso_fst : f.modulePullback.obj (idealModule t1) ≅ idealModule i1 :=
  sourceIdealIsoOfStrictFlat
    { upper := i1, left := f, right := f1', lower := t1, cell := S.comm1 }
    S.strict1 S.flat1

/-- Strictness and flatness identify the second pulled-back base ideal with the source ideal. -/
def idealIso_snd : f.modulePullback.obj (idealModule t2) ≅ idealModule i2 :=
  sourceIdealIsoOfStrictFlat
    { upper := i2, left := f, right := f2', lower := t2, cell := S.comm2 }
    S.strict2 S.flat2

/-- The first ideal isomorphism has the canonical ideal comparison as forward map. -/
theorem idealIso_fst_hom : (idealIso_fst S).hom = idealMap_fst S := rfl

/-- The second ideal isomorphism has the canonical ideal comparison as forward map. -/
theorem idealIso_snd_hom : (idealIso_snd S).hom = idealMap_snd S := rfl

/-- The first canonical ideal comparison is invertible by the explicit strict-flat comparison. -/
theorem idealMap_fst_isIso : IsIso (idealMap_fst S) :=
  (idealIso_fst S).isIso_hom

/-- The second canonical ideal comparison is invertible by the explicit strict-flat comparison. -/
theorem idealMap_snd_isIso : IsIso (idealMap_snd S) :=
  (idealIso_snd S).isIso_hom

/-- Tensoring the first explicit ideal comparison identifies its coefficient modules. -/
def idealTensorIso_fst :
    moduleTensor (f.modulePullback.obj (idealModule t1)) S.module ≅
      moduleTensor (idealModule i1) S.module :=
  (Tensor.rightFunctor S.module).mapIso (idealIso_fst S)

/-- Tensoring the second explicit ideal comparison identifies its coefficient modules. -/
def idealTensorIso_snd :
    moduleTensor (f.modulePullback.obj (idealModule t2)) S.module ≅
      moduleTensor (idealModule i2) S.module :=
  (Tensor.rightFunctor S.module).mapIso (idealIso_snd S)

/-- The first tensor comparison is induced by the canonical ideal map and the identity. -/
theorem idealTensorIso_fst_hom :
    (idealTensorIso_fst S).hom = moduleTensorMap (idealMap_fst S) (𝟙 S.module) := by
  exact (CategoryTheory.MonoidalCategory.tensorHom_id (idealMap_fst S) S.module).symm

/-- The second tensor comparison is induced by the canonical ideal map and the identity. -/
theorem idealTensorIso_snd_hom :
    (idealTensorIso_snd S).hom = moduleTensorMap (idealMap_snd S) (𝟙 S.module) := by
  exact (CategoryTheory.MonoidalCategory.tensorHom_id (idealMap_snd S) S.module).symm

variable [(SheafOfModules.restrictScalars.{max uC vC} S.base.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (t1.comp S.base).structureMap).IsRightAdjoint]

/-- The canonical coefficient map is pullback of the horizontal base ideal map tensored
with the identity of the module. -/
def pullbackIdealTensorMap :
    moduleTensor (f.modulePullback.obj (idealModule t2)) S.module ⟶
      moduleTensor (f.modulePullback.obj (idealModule t1)) S.module :=
  moduleTensorMap (f.modulePullback.map (idealHom S.base S.over_base)) (𝟙 S.module)

/-- The coefficient map is the tensor morphism of the pulled-back base ideal map and identity. -/
theorem pullbackIdealTensorMap_spec :
    pullbackIdealTensorMap S =
      moduleTensorMap (f.modulePullback.map (idealHom S.base S.over_base)) (𝟙 S.module) := rfl

variable [(SheafOfModules.restrictScalars.{max uC vC} S.h.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (i1.comp S.h).structureMap).IsRightAdjoint]

/-- The canonical coefficient map and horizontal source ideal map commute with the
two strict-flat ideal comparisons after tensoring with the module. -/
theorem pullbackIdealTensor_commSq :
    CommSq (moduleTensorMap (idealMap_snd S) (𝟙 S.module)) (pullbackIdealTensorMap S)
      (moduleTensorMap (idealHom S.h S.over_source) (𝟙 S.module))
      (moduleTensorMap (idealMap_fst S) (𝟙 S.module)) := by
  sorry

variable [HasWeakSheafify JC CommRingCat.{max uC vC}]
variable [JC.WEqualsLocallyBijective CommRingCat.{max uC vC}]
variable [HasSheafify JC AddCommGrpCat.{max uC vC}]
variable [(SheafOfModules.restrictScalars (ringSheafMap (normalizedProjection i1))).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars (ringSheafMap (normalizedProjection i2))).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max uC vC}
  (ringSheaf JC (normalizedRing i1))]
variable [SheafOfModules.Localization.HasLowerShriek.{max uC vC}
  (ringSheaf JC (normalizedRing i2))]
variable [HasFunctorialInjectives
  (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)]
variable [HasExt.{wExt} (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)]

/-- In a coherent strict flat square of first-order thickenings, coefficient
postcomposition carries the second identity-infinitesimal existence obstruction
to the first identity-infinitesimal existence obstruction. -/
theorem obstruction_map :
    (Ext.mk₀ (pullbackIdealTensorMap S)).postcomp S.module (add_zero 2)
        (existenceObstruction i2 S.module
          (moduleTensor (f.modulePullback.obj (idealModule t2)) S.module)
          (idealTensorIso_snd S).inv) =
      existenceObstruction i1 S.module
        (moduleTensor (f.modulePullback.obj (idealModule t1)) S.module)
        (idealTensorIso_fst S).inv := by
  sorry

end FlatMorphismSquare

end RingedSite.ToposHom.Thickening
