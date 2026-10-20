/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.RelativeDiagram
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.RelativeDiagram
import StacksCheckRecall

open CategoryTheory

universe uC2 vC2 uC2p vC2p uB2 vB2 uB2p vB2p uC1 vC1 uC1p vC1p uB1 vB1 uB1p vB1p w

/- 91.13.1.2: the relative diagram over an open cube of ringed topoi whose four
horizontal arrows are first-order thickenings. The kernel modules carry their
canonical exact rows and comparison maps c₁ and c₂. The prescribed map
ν : g⁻¹𝒢₁ ⟶ 𝒢₂ is linear over g⁻¹𝒪₁ and is compatible with the base kernel
comparison after canonical pullback transport. The site presentations are
independent, and the thickened connecting morphism is absent. -/
@[stacks 08UI] #check (RingedSite.ToposHom.Thickening.RelativeDiagram :
  ∀ {C2 : RingedSite.{uC2, vC2, w}}
    {C2' : RingedSite.{uC2p, vC2p, w}}
    {B2 : RingedSite.{uB2, vB2, w}}
    {B2' : RingedSite.{uB2p, vB2p, w}}
    {C1 : RingedSite.{uC1, vC1, w}}
    {C1' : RingedSite.{uC1p, vC1p, w}}
    {B1 : RingedSite.{uB1, vB1, w}}
    {B1' : RingedSite.{uB1p, vB1p, w}}
    [C2.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B2.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C1.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B1.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C2.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [C2'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B2.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B2'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [C1.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [C1'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B1.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [B1'.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasSheafify C2'.siteTopology AddCommGrpCat.{w}]
    [C2'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify B2'.siteTopology AddCommGrpCat.{w}]
    [B2'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify C1'.siteTopology AddCommGrpCat.{w}]
    [C1'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify B1'.siteTopology AddCommGrpCat.{w}]
    [B1'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

    {back : RingedSite.ToposHom.CommSquare C2 C2' B2 B2'} {front : RingedSite.ToposHom.CommSquare C1 C1' B1 B1'}
    [RingedSite.ToposHom.IsFirstOrderThickening front.upper] [RingedSite.ToposHom.IsFirstOrderThickening front.lower]
    [RingedSite.ToposHom.IsFirstOrderThickening back.upper] [RingedSite.ToposHom.IsFirstOrderThickening back.lower]
    (Q : RingedSite.ToposHom.OpenCube back front)
    [(SheafOfModules.restrictScalars.{w} front.left.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} front.right.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} front.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} front.lower.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} back.left.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} back.right.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} back.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} back.lower.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp front.left front.lower).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp front.upper front.right).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp back.left back.lower).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp back.upper back.right).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} Q.g.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} Q.base.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} Q.base'.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp Q.base front.lower).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp back.lower Q.base').structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp Q.g front.left).structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (RingedSite.ToposHom.comp back.left Q.base).structureMap).IsRightAdjoint],
    Type (max uC2 w))
