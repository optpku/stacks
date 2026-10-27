/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.RelativeDiagram
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.ModuleObstruction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.RelativeDiagram

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open CategoryTheory.Sheaf.InternalModule

noncomputable section

set_option backward.privateInPublic true

universe uX vX uY vY uZ vZ uW vW w

namespace RingedSite.ToposHom.Thickening

section RingTransport

variable {X : Type uX} [Category.{vX} X] {JX : GrothendieckTopology X}
variable {Y : Type uY} [Category.{vY} Y] {JY : GrothendieckTopology Y}
variable {Z : Type uZ} [Category.{vZ} Z] {JZ : GrothendieckTopology Z}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JZ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
variable [JY.HasSheafCompose (forget RingCat.{w})]
variable [JZ.HasSheafCompose (forget RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable {OZ : Sheaf JZ CommRingCat.{w}}

set_option maxHeartbeats 1600000 in
private def commRingCompIso
    (f : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
    (g : ToposHom (ofCommRingSheaf JY OY) (ofCommRingSheaf JZ OZ))
    (A : Sheaf JZ CommRingCat.{w}) :
    (f.comp g).toTopos.commRingInverseImage.obj A ≅
      f.toTopos.commRingInverseImage.obj (g.toTopos.commRingInverseImage.obj A) :=
  (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing (J := JX)).preimageIso
    ((f.comp g).toTopos.commRingInverseImageForgetRingIso.app A ≪≫
      (MorphismOfTopoiIn.ringInverseImageCompIso g.toTopos f.toTopos).app
        (ringSheaf JZ A) ≪≫
      f.toTopos.ringInverseImage.mapIso
        (g.toTopos.commRingInverseImageForgetRingIso.app A).symm ≪≫
      (f.toTopos.commRingInverseImageForgetRingIso.app
        (g.toTopos.commRingInverseImage.obj A)).symm)

set_option maxHeartbeats 1600000 in
private def commRingCellIso
    {f g : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY)}
    (e : TwoIso f g) (A : Sheaf JY CommRingCat.{w}) :
    f.toTopos.commRingInverseImage.obj A ≅ g.toTopos.commRingInverseImage.obj A :=
  (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing (J := JX)).preimageIso
    (f.toTopos.commRingInverseImageForgetRingIso.app A ≪≫
      (MorphismOfTopoiIn.ringInverseImageNatIso
        (inverseImageIsoOfPushforwardIso f g e.homIso)).app (ringSheaf JY A) ≪≫
      (g.toTopos.commRingInverseImageForgetRingIso.app A).symm)

set_option maxHeartbeats 1600000 in
private def commRingSquareMap
    {W : Type uW} [Category.{vW} W] {JW : GrothendieckTopology W}
    [JW.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JW.HasSheafCompose (forget RingCat.{w})] {OW : Sheaf JW CommRingCat.{w}}
    (sq : CommSquare (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY)
      (ofCommRingSheaf JZ OZ) (ofCommRingSheaf JW OW)) :
    sq.left.toTopos.commRingInverseImage.obj (normalizedRing sq.lower) ⟶
      normalizedRing sq.upper :=
  (commRingCompIso sq.left sq.lower OW).inv ≫
    (commRingCellIso sq.cell OW).inv ≫
    (commRingCompIso sq.upper sq.right OW).hom ≫
    sq.upper.toTopos.commRingInverseImage.map (normalizedProjection sq.right)

section KernelTransport

variable [JX.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JY.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify JX CommRingCat.{w}] [JX.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify JX AddCommGrpCat.{w}] [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY CommRingCat.{w}] [JY.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}] [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : MorphismOfTopoiIn.{uY, uX, vY, vX, w} JY JX)
variable {A B : Sheaf JY CommRingCat.{w}} (π : A ⟶ B)
variable [hπ : SheafOfModules.RingedSite.IsFirstOrderThickening π]
variable [hp : SheafOfModules.RingedSite.IsFirstOrderThickening (f.commRingInverseImage.map π)]

set_option maxHeartbeats 1600000 in
private def pulledIdealInclusion :
    (ToInternal.underlying (ringSheaf JX (f.commRingInverseImage.obj B))).obj
      (FirstOrderThickening.ideal (f.commRingInverseImage.map π)) ⟶
    f.inverseImage.obj ((ToInternal.underlying (ringSheaf JY A)).obj
      (SheafOfModules.unit (ringSheaf JY A))) :=
  (ToInternal.underlying (ringSheaf JX (f.commRingInverseImage.obj A))).map
      ((FirstOrderThickening.ideal_forgetIso (f.commRingInverseImage.map π)).hom ≫
        KernelIdeal.ι (f.commRingInverseImage.map π)) ≫
    (sheafCompose JX (forget RingCat.{w})).map
      (f.commRingInverseImageForgetRingIso.hom.app A) ≫
    (f.ringInverseImageForgetIso.hom.app (ringSheaf JY A))

set_option maxHeartbeats 1600000 in
private def pulledIdealCondition : Prop :=
  pulledIdealInclusion f π ≫
      (ToInternal.underlying (ringSheaf JY A) ⋙ f.inverseImage).map (KernelIdeal.map π) =
    pulledIdealInclusion f π ≫
      (ToInternal.underlying (ringSheaf JY A) ⋙ f.inverseImage).map
        (0 : _ ⟶ (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
          (SheafOfModules.unit (ringSheaf JY B)))

set_option maxHeartbeats 1600000 in
private def pulledIdealCarrier (h : pulledIdealCondition f π) :
    (ToInternal.underlying (ringSheaf JX (f.commRingInverseImage.obj B))).obj
      (FirstOrderThickening.ideal (f.commRingInverseImage.map π)) ⟶
    f.inverseImage.obj ((ToInternal.underlying (ringSheaf JY B)).obj
      (FirstOrderThickening.ideal π)) := by
  let F := ToInternal.underlying (ringSheaf JY A)
  have forgetComposite : PreservesFiniteLimits
      (sheafCompose JY (forget AddCommGrpCat.{w}) ⋙
        sheafToPresheaf JY (Type w)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf JY AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}))
    infer_instance
  have forgetful : PreservesFiniteLimits
      (sheafCompose JY (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have preserveF : PreservesFiniteLimits F := comp_preservesFiniteLimits
    (SheafOfModules.toSheaf _) (sheafCompose JY (forget AddCommGrpCat.{w}))
  have preserveFG : PreservesFiniteLimits (F ⋙ f.inverseImage) :=
    comp_preservesFiniteLimits F f.inverseImage
  have preserve : PreservesLimit (parallelPair (KernelIdeal.map π) 0) (F ⋙ f.inverseImage) :=
    @PreservesLimitsOfShape.preservesLimit _ _ _ _ _ _ (F ⋙ f.inverseImage)
      (preserveFG.preservesFiniteLimits WalkingParallelPair) _
  let comparison := @PreservesEqualizer.iso _ _ _ _ (F ⋙ f.inverseImage) _ _
    (KernelIdeal.map π) 0 inferInstance inferInstance preserve
  exact equalizer.lift (pulledIdealInclusion f π) h ≫ comparison.inv ≫
    f.inverseImage.map (F.map ((kernelSubobjectIso (KernelIdeal.map π)).inv ≫
      (FirstOrderThickening.ideal_forgetIso π).inv))

end KernelTransport

end RingTransport

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


namespace RelativeDiagram

set_option maxHeartbeats 1600000 in
/-- The front upper square-zero projection transported to the source site of the cube. -/
def normalizedFrontUpper :=
  Q.g.toTopos.commRingInverseImage.map (normalizedProjection front.upper)

set_option maxHeartbeats 1600000 in
/-- The front lower square-zero projection transported along the left face to the source site. -/
def normalizedFrontLower :=
  Q.g.toTopos.commRingInverseImage.map
    (front.left.toTopos.commRingInverseImage.map (normalizedProjection front.lower))

set_option maxHeartbeats 1600000 in
/-- The back lower square-zero projection transported to the source site. -/
def normalizedBackLower :=
  back.left.toTopos.commRingInverseImage.map (normalizedProjection back.lower)

set_option maxHeartbeats 1600000 in
private def normalizedF1 :=
  Q.g.toTopos.commRingInverseImage.map (normalizedProjection front.left)

set_option maxHeartbeats 1600000 in
private def normalizedF1' :=
  Q.g.toTopos.commRingInverseImage.map (commRingSquareMap front)

set_option maxHeartbeats 1600000 in
private def normalizedF2' := commRingSquareMap back

set_option maxHeartbeats 1600000 in
private def normalizedT :=
  (commRingCompIso Q.g front.left OB1).inv ≫
    (commRingCellIso Q.leftCell OB1).hom ≫
    (commRingCompIso back.left Q.base OB1).hom ≫
    back.left.toTopos.commRingInverseImage.map (normalizedProjection Q.base)

set_option maxHeartbeats 1600000 in
private def normalizedT' :=
  (commRingCompIso Q.g front.left (normalizedRing front.lower)).inv ≫
    (commRingCellIso Q.leftCell (normalizedRing front.lower)).hom ≫
    (commRingCompIso back.left Q.base (normalizedRing front.lower)).hom ≫
    back.left.toTopos.commRingInverseImage.map
      ((commRingCompIso Q.base front.lower OB1p).inv ≫
        (commRingCellIso Q.lowerCell OB1p).inv ≫
        (commRingCompIso back.lower Q.base' OB1p).hom ≫
        back.lower.toTopos.commRingInverseImage.map (normalizedProjection Q.base'))

set_option maxHeartbeats 1600000 in
private def normalizedFaces : Prop :=
  normalizedF1' Q ≫ normalizedFrontUpper Q = normalizedFrontLower Q ≫ normalizedF1 Q ∧
    normalizedF2' (back := back) ≫ normalizedProjection back.upper =
      normalizedBackLower (back := back) ≫ normalizedProjection back.left ∧
    normalizedT' Q ≫ normalizedBackLower (back := back) =
      normalizedFrontLower Q ≫ normalizedT Q ∧
    normalizedT Q ≫ normalizedProjection back.left =
      normalizedF1 Q ≫ normalizedProjection Q.g

set_option maxHeartbeats 1600000 in
private def normalizedNuCarrier (D : RelativeDiagram Q)
    (h1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q))
    (p : pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1)) :
    (ToInternal.underlying (ringSheaf JC2 (normalizedRing Q.g))).obj
        (FirstOrderThickening.ideal (normalizedFrontUpper Q) (hπ := h1)) ⟶
      (ToInternal.underlying (ringSheaf JC2 (normalizedRing Q.g))).obj
        ((restrictionAlong (normalizedProjection Q.g)).obj
          (FirstOrderThickening.ideal (normalizedProjection back.upper)
            (hπ := normalizedProjection_isFirstOrderThickening back.upper))) :=
  pulledIdealCarrier Q.g.toTopos (normalizedProjection front.upper)
      (hπ := normalizedProjection_isFirstOrderThickening front.upper) (hp := h1) p ≫
    Q.g.toTopos.inverseImage.map
      ((ToInternal.underlying (ringSheaf JC1 OC1)).map (normalizedIdealIso front.upper).hom) ≫
    (Q.g.toTopos.moduleInverseImageForgetIso (ringSheaf JC1 OC1)).inv.app
      (idealModule front.upper) ≫
    (ToInternal.underlying (Q.g.toTopos.ringInverseImage.obj (ringSheaf JC1 OC1))).map D.ν ≫
    (ToInternal.underlying (ringSheaf JC2 OC2)).map (normalizedIdealIso back.upper).inv

set_option maxHeartbeats 1600000 in
private def normalizedNuLinear (D : RelativeDiagram Q)
    (h1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q))
    (p : pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1)) : Prop :=
  (∀ U (x y : (FirstOrderThickening.ideal (normalizedFrontUpper Q) (hπ := h1)).val.obj U),
    underlyingApp (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) U (x + y) =
      underlyingApp (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) U x +
        underlyingApp (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) U y) ∧
  (∀ U (r : (ringSheaf JC2 (normalizedRing Q.g)).obj.obj U)
      (x : (FirstOrderThickening.ideal (normalizedFrontUpper Q) (hπ := h1)).val.obj U),
    underlyingApp (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) U
      (((FirstOrderThickening.ideal (normalizedFrontUpper Q) (hπ := h1)).val.obj U).isModule.smul r x) =
      (((SheafOfModules.RingedSite.restrictionAlong (normalizedProjection Q.g)).obj
        (FirstOrderThickening.ideal (normalizedProjection back.upper)
          (hπ := normalizedProjection_isFirstOrderThickening back.upper))).val.obj U).isModule.smul
            r (underlyingApp (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) U x))

set_option maxHeartbeats 1600000 in
private def normalizedNu (D : RelativeDiagram Q)
    (h1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q))
    (p : pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1))
    (q : normalizedNuLinear Q D h1 p) :
    FirstOrderThickening.ideal (normalizedFrontUpper Q) (hπ := h1) ⟶
      (restrictionAlong (normalizedProjection Q.g)).obj
        (FirstOrderThickening.ideal (normalizedProjection back.upper)
          (hπ := normalizedProjection_isFirstOrderThickening back.upper)) :=
  homOfUnderlying (ringSheaf JC2 (normalizedRing Q.g)) (normalizedNuCarrier Q D h1 p) q.1 q.2

set_option maxHeartbeats 1600000 in
private def normalizedKernel (D : RelativeDiagram Q)
    (h1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q))
    (hb1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontLower Q))
    (hb2 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedBackLower (back := back)))
    (p : pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1))
    (q : normalizedNuLinear Q D h1 p) (faces : normalizedFaces Q) : Prop :=
  FirstOrderThickening.toAdditive (normalizedF1 Q)
      (@FirstOrderThickening.inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ (normalizedFrontLower Q) (normalizedF1 Q)
        (normalizedFrontUpper Q) (normalizedF1' Q) hb1 h1 faces.1) ≫
    FirstOrderThickening.toAdditive (normalizedProjection Q.g) (normalizedNu Q D h1 p q) =
  FirstOrderThickening.toAdditive (normalizedT Q)
      (@FirstOrderThickening.inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ (normalizedFrontLower Q) (normalizedT Q)
        (normalizedBackLower (back := back)) (normalizedT' Q) hb1 hb2 faces.2.2.1) ≫
    FirstOrderThickening.toAdditive (normalizedProjection back.left)
      (@FirstOrderThickening.inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _ (normalizedBackLower (back := back))
        (normalizedProjection back.left) (normalizedProjection back.upper)
        (normalizedF2' (back := back)) hb2
        (normalizedProjection_isFirstOrderThickening back.upper) faces.2.1)

set_option maxHeartbeats 1600000 in
/-- Inverse image preserves the four square-zero projections and transports the kernel
compatibility square to the source site. -/
private theorem normalizedDiagram_laws (D : RelativeDiagram Q) :
    (SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q) ∧
      SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontLower Q) ∧
      SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedBackLower (back := back))) ∧
    normalizedFaces Q ∧
    (∀ h1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q),
      pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1) ∧
      ∀ p : pulledIdealCondition Q.g.toTopos (normalizedProjection front.upper) (hp := h1),
        normalizedNuLinear Q D h1 p ∧
        ∀ q : normalizedNuLinear Q D h1 p,
          ∀ hb1 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontLower Q),
          ∀ hb2 : SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedBackLower (back := back)),
          ∀ faces : normalizedFaces Q, normalizedKernel Q D h1 hb1 hb2 p q faces) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- The front upper projection remains a first-order thickening on the source site. -/
theorem normalizedFrontUpper_isFirstOrderThickening (D : RelativeDiagram Q) :
    SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontUpper Q) :=
  (normalizedDiagram_laws Q D).1.1

set_option maxHeartbeats 1600000 in
/-- The front lower projection remains a first-order thickening on the source site. -/
theorem normalizedFrontLower_isFirstOrderThickening (D : RelativeDiagram Q) :
    SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedFrontLower Q) :=
  (normalizedDiagram_laws Q D).1.2.1

set_option maxHeartbeats 1600000 in
/-- The back lower projection remains a first-order thickening on the source site. -/
theorem normalizedBackLower_isFirstOrderThickening (D : RelativeDiagram Q) :
    SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedBackLower (back := back)) :=
  (normalizedDiagram_laws Q D).1.2.2

set_option maxHeartbeats 1600000 in
/-- The inverse-image reduction of an open cube with its prescribed kernel map is a
relative diagram of first-order ring-sheaf thickenings on the source site. -/
def normalizedDiagram (D : RelativeDiagram Q) :
    FirstOrderThickening.RelativeDiagram
      (hπO1 := normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := normalizedBackLower_isFirstOrderThickening Q D)
      (normalizedFrontUpper Q) (normalizedFrontLower Q)
      (normalizedProjection back.upper) (normalizedBackLower (back := back)) := by
  let laws := normalizedDiagram_laws Q D
  let h1 := laws.1.1
  let hb1 := laws.1.2.1
  let hb2 := laws.1.2.2
  let p := (laws.2.2 h1).1
  let q := ((laws.2.2 h1).2 p).1
  exact @FirstOrderThickening.RelativeDiagram.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (normalizedFrontUpper Q) (normalizedFrontLower Q)
    (normalizedProjection back.upper) (normalizedBackLower (back := back))
    h1 hb1 (normalizedProjection_isFirstOrderThickening back.upper) hb2
    (normalizedF1 Q) (normalizedF1' Q) laws.2.1.1
    (normalizedProjection back.left) (normalizedF2' (back := back)) laws.2.1.2.1
    (normalizedProjection Q.g) (normalizedT Q) (normalizedT' Q)
    laws.2.1.2.2.1 laws.2.1.2.2.2 (normalizedNu Q D h1 p q)
    (((laws.2.2 h1).2 p).2 q hb1 hb2 laws.2.1)

set_option maxHeartbeats 1600000 in
/-- The normalized relative diagram uses the inverse-image structure map of the diagonal
and the transported original left structure map. -/
theorem normalizedDiagram_spec (D : RelativeDiagram Q) :
    FirstOrderThickening.RelativeDiagram.g (hπO1 := normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := normalizedBackLower_isFirstOrderThickening Q D) (normalizedDiagram Q D) =
      normalizedProjection Q.g ∧
    FirstOrderThickening.RelativeDiagram.f1 (hπO1 := normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := normalizedBackLower_isFirstOrderThickening Q D) (normalizedDiagram Q D) =
      Q.g.toTopos.commRingInverseImage.map (normalizedProjection front.left) := by
  sorry

end RelativeDiagram

end RingedSite.ToposHom.Thickening
