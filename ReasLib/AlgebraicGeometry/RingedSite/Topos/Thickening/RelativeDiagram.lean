/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Cube
import Mathlib.Tactic.DSimpPercent

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uC2 vC2 uC2p vC2p uB2 vB2 uB2p vB2p uC1 vC1 uC1p vC1p uB1 vB1 uB1p vB1p w

namespace RingedSite.ToposHom.Thickening

variable {C2 : RingedSite.{uC2, vC2, w}}
variable {C2' : RingedSite.{uC2p, vC2p, w}}
variable {B2 : RingedSite.{uB2, vB2, w}}
variable {B2' : RingedSite.{uB2p, vB2p, w}}
variable {C1 : RingedSite.{uC1, vC1, w}}
variable {C1' : RingedSite.{uC1p, vC1p, w}}
variable {B1 : RingedSite.{uB1, vB1, w}}
variable {B1' : RingedSite.{uB1p, vB1p, w}}
variable [C2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C2.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C2'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B2.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B2'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C1.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C1'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B1.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B1'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify C2'.siteTopology AddCommGrpCat.{w}]
variable [C2'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify B2'.siteTopology AddCommGrpCat.{w}]
variable [B2'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify C1'.siteTopology AddCommGrpCat.{w}]
variable [C1'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify B1'.siteTopology AddCommGrpCat.{w}]
variable [B1'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {back : CommSquare C2 C2' B2 B2'} {front : CommSquare C1 C1' B1 B1'}
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

/-- A relative diagram over an open cube of first-order thickenings consists of an
inverse-image-linear map between the upper kernel modules compatible with the canonical
kernel comparisons on the front, back, and lower faces. -/
structure RelativeDiagram where
  /-- The prescribed inverse-image-linear morphism between the upper kernel modules. -/
  ν : (Q.g.toTopos.moduleInverseImage C1.structureSheaf).obj (idealModule front.upper) ⟶
      (SheafOfModules.restrictScalars Q.g.structureMap).obj (idealModule back.upper)
  /-- The canonical kernel comparison square commutes after pullback transport. -/
  comm_kernel :
    (modulePullbackCompIso Q.g front.left).hom.app (idealModule front.lower) ≫
        Q.g.modulePullback.map (sourceIdealMap front) ≫ (ModulePullback.scalarHomEquiv Q.g _ _).symm ν =
      (modulePullbackIsoOfTwoIso Q.leftCell).hom.app (idealModule front.lower) ≫
        (modulePullbackCompIso back.left Q.base).hom.app (idealModule front.lower) ≫
          back.left.modulePullback.map (sourceIdealMap (dsimp% only [OpenCube.lowerSquare] Q.lowerSquare)) ≫ sourceIdealMap back

namespace RelativeDiagram

/-- Assemble a relative diagram from its inverse-image-linear kernel map and compatibility
with the canonical kernel comparisons. -/
def of (ν : (Q.g.toTopos.moduleInverseImage C1.structureSheaf).obj (idealModule front.upper) ⟶
      (SheafOfModules.restrictScalars Q.g.structureMap).obj (idealModule back.upper))
    (comm_kernel :
      (modulePullbackCompIso Q.g front.left).hom.app (idealModule front.lower) ≫
        Q.g.modulePullback.map (sourceIdealMap front) ≫ (ModulePullback.scalarHomEquiv Q.g _ _).symm ν =
      (modulePullbackIsoOfTwoIso Q.leftCell).hom.app (idealModule front.lower) ≫
        (modulePullbackCompIso back.left Q.base).hom.app (idealModule front.lower) ≫
          back.left.modulePullback.map (sourceIdealMap (dsimp% only [OpenCube.lowerSquare] Q.lowerSquare)) ≫ sourceIdealMap back) :
    RelativeDiagram Q where
  ν := ν
  comm_kernel := comm_kernel

variable {Q}

/-- The scalar-adjoint pullback-linear form of the prescribed inverse-image-linear map. -/
def νPullback (D : RelativeDiagram Q) :
    Q.g.modulePullback.obj (idealModule front.upper) ⟶ idealModule back.upper :=
  (ModulePullback.scalarHomEquiv Q.g _ _).symm D.ν

/-- The front inverse-image-linear kernel comparison is the scalar adjoint of its
canonical pullback-linear comparison. -/
def c1 (D : RelativeDiagram Q) :
    (front.left.toTopos.moduleInverseImage B1.structureSheaf).obj (idealModule front.lower) ⟶
      (SheafOfModules.restrictScalars front.left.structureMap).obj (idealModule front.upper) :=
  ModulePullback.scalarHomEquiv front.left _ _ (sourceIdealMap front)

/-- The back inverse-image-linear kernel comparison is the scalar adjoint of its
canonical pullback-linear comparison. -/
def c2 (D : RelativeDiagram Q) :
    (back.left.toTopos.moduleInverseImage B2.structureSheaf).obj (idealModule back.lower) ⟶
      (SheafOfModules.restrictScalars back.left.structureMap).obj (idealModule back.upper) :=
  ModulePullback.scalarHomEquiv back.left _ _ (sourceIdealMap back)

/-- Scalar adjunction sends the pullback-linear kernel map back to the prescribed map. -/
theorem νPullback_spec (D : RelativeDiagram Q) :
    ModulePullback.scalarHomEquiv Q.g _ _ D.νPullback = D.ν :=
  (ModulePullback.scalarHomEquiv Q.g _ _).apply_symm_apply D.ν

/-- The pullback-linear kernel map commutes with the canonically transported kernel
comparisons. -/
theorem spec_kernel (D : RelativeDiagram Q) :
    (modulePullbackCompIso Q.g front.left).hom.app (idealModule front.lower) ≫
        Q.g.modulePullback.map (sourceIdealMap front) ≫ D.νPullback =
      (modulePullbackIsoOfTwoIso Q.leftCell).hom.app (idealModule front.lower) ≫
        (modulePullbackCompIso back.left Q.base).hom.app (idealModule front.lower) ≫
          back.left.modulePullback.map (sourceIdealMap (dsimp% only [OpenCube.lowerSquare] Q.lowerSquare)) ≫ sourceIdealMap back :=
  D.comm_kernel

end RelativeDiagram

end RingedSite.ToposHom.Thickening
