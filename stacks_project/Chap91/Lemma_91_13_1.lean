/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.MapObstruction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe w

namespace RingedSite.ToposHom.Thickening

universe uC2 vC2 uC2p vC2p uB2 vB2 uB2p vB2p uC1 vC1 uC1p vC1p uB1 vB1 uB1p vB1p

variable {C2 : Type uC2} [Category.{vC2} C2] {JC2 : GrothendieckTopology C2}
variable [JC2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC2.HasSheafCompose (forget RingCat.{w})]
variable [JC2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC2 AddCommGrpCat.{w}] [JC2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC2 CommRingCat.{w}] [JC2.WEqualsLocallyBijective CommRingCat.{w}]
variable {OC2 : Sheaf JC2 CommRingCat.{w}}

variable {C2p : Type uC2p} [Category.{vC2p} C2p] {JC2p : GrothendieckTopology C2p}
variable [JC2p.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC2p.HasSheafCompose (forget RingCat.{w})]
variable [JC2p.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC2p AddCommGrpCat.{w}] [JC2p.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC2p CommRingCat.{w}] [JC2p.WEqualsLocallyBijective CommRingCat.{w}]
variable {OC2p : Sheaf JC2p CommRingCat.{w}}

variable {B2 : Type uB2} [Category.{vB2} B2] {JB2 : GrothendieckTopology B2}
variable [JB2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB2.HasSheafCompose (forget RingCat.{w})]
variable [JB2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JB2 AddCommGrpCat.{w}] [JB2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JB2 CommRingCat.{w}] [JB2.WEqualsLocallyBijective CommRingCat.{w}]
variable {OB2 : Sheaf JB2 CommRingCat.{w}}

variable {B2p : Type uB2p} [Category.{vB2p} B2p] {JB2p : GrothendieckTopology B2p}
variable [JB2p.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB2p.HasSheafCompose (forget RingCat.{w})]
variable [JB2p.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JB2p AddCommGrpCat.{w}] [JB2p.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JB2p CommRingCat.{w}] [JB2p.WEqualsLocallyBijective CommRingCat.{w}]
variable {OB2p : Sheaf JB2p CommRingCat.{w}}

variable {C1 : Type uC1} [Category.{vC1} C1] {JC1 : GrothendieckTopology C1}
variable [JC1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC1.HasSheafCompose (forget RingCat.{w})]
variable [JC1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC1 AddCommGrpCat.{w}] [JC1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC1 CommRingCat.{w}] [JC1.WEqualsLocallyBijective CommRingCat.{w}]
variable {OC1 : Sheaf JC1 CommRingCat.{w}}

variable {C1p : Type uC1p} [Category.{vC1p} C1p] {JC1p : GrothendieckTopology C1p}
variable [JC1p.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC1p.HasSheafCompose (forget RingCat.{w})]
variable [JC1p.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC1p AddCommGrpCat.{w}] [JC1p.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC1p CommRingCat.{w}] [JC1p.WEqualsLocallyBijective CommRingCat.{w}]
variable {OC1p : Sheaf JC1p CommRingCat.{w}}

variable {B1 : Type uB1} [Category.{vB1} B1] {JB1 : GrothendieckTopology B1}
variable [JB1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB1.HasSheafCompose (forget RingCat.{w})]
variable [JB1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JB1 AddCommGrpCat.{w}] [JB1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JB1 CommRingCat.{w}] [JB1.WEqualsLocallyBijective CommRingCat.{w}]
variable {OB1 : Sheaf JB1 CommRingCat.{w}}

variable {B1p : Type uB1p} [Category.{vB1p} B1p] {JB1p : GrothendieckTopology B1p}
variable [JB1p.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB1p.HasSheafCompose (forget RingCat.{w})]
variable [JB1p.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JB1p AddCommGrpCat.{w}] [JB1p.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JB1p CommRingCat.{w}] [JB1p.WEqualsLocallyBijective CommRingCat.{w}]
variable {OB1p : Sheaf JB1p CommRingCat.{w}}

variable {back : CommSquare (ofCommRingSheaf JC2 OC2) (ofCommRingSheaf JC2p OC2p)
  (ofCommRingSheaf JB2 OB2) (ofCommRingSheaf JB2p OB2p)}
variable {front : CommSquare (ofCommRingSheaf JC1 OC1) (ofCommRingSheaf JC1p OC1p)
  (ofCommRingSheaf JB1 OB1) (ofCommRingSheaf JB1p OB1p)}
variable [IsFirstOrderThickening front.upper] [IsFirstOrderThickening front.lower]
variable [IsFirstOrderThickening back.upper] [IsFirstOrderThickening back.lower]
variable (Q : OpenCube back front)
variable [(SheafOfModules.restrictScalars.{w} front.left.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} front.right.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} front.upper.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} front.lower.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} back.left.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} back.right.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} back.upper.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} back.lower.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp front.left front.lower).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp front.upper front.right).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp back.left back.lower).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp back.upper back.right).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} Q.g.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} Q.base.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} Q.base'.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp Q.base front.lower).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp back.lower Q.base').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp Q.g front.left).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp back.left Q.base).structureMap).IsRightAdjoint]

variable [UnivLE.{max uC2 vC2, w}]

/- Lemma 91.13.1. For the open cube of ringed topoi, the prescribed compatible
inverse-image-linear kernel map has a canonical Ext¹ obstruction. It vanishes
exactly when a compatible missing morphism exists. -/
@[stacks 08UG] #check (RingedSite.ToposHom.Thickening.mapObstruction_eq_zero_iff Q :
  ∀ D : RelativeDiagram Q, mapObstruction Q D = 0 ↔ Nonempty (FittingMap Q D))

#check (RingedSite.ToposHom.Thickening.mapObstruction Q :
  RelativeDiagram Q → Ext⁽(1 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back)))

#check (RingedSite.ToposHom.Thickening.fittingMap_principalHomogeneous Q :
  ∀ (D : RelativeDiagram Q) (φ φ' : FittingMap Q D),
    ∃! α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper),
      FittingMap.perturb α φ = φ')

#check (RingedSite.ToposHom.Thickening.homOmegaPushforwardEquiv Q :
  (Ω(normalizedProjection front.left) ⟶ Q.g.modulePushforward.obj (idealModule back.upper)) ≃+
    (Q.g.modulePullback.obj Ω(normalizedProjection front.left) ⟶ idealModule back.upper))

#check (RingedSite.ToposHom.Thickening.homOmegaExtZeroEquiv Q :
  (Ω(normalizedProjection front.left) ⟶ Q.g.modulePushforward.obj (idealModule back.upper)) ≃+
    Ext⁽(0 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back)))

end RingedSite.ToposHom.Thickening
