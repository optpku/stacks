/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Normalization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FittingMap
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

set_option backward.privateInPublic true

universe uX vX uY vY w

namespace RingedSite.ToposHom.Thickening

section InverseTopos

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (i : ToposHom X Y) [IsFirstOrderThickening i]

set_option maxHeartbeats 1600000 in
private def pushforwardEquivalence :
    Sheaf X.siteTopology (Type w) ≌ Sheaf Y.siteTopology (Type w) :=
  i.toTopos.pushforward.asEquivalence

set_option maxHeartbeats 1600000 in
private def inverseTopos : MorphismOfTopoiIn X.siteTopology Y.siteTopology where
  inverseImageFunctor := ⟨i.toTopos.pushforward,
    @PreservesLimits.preservesFiniteLimits _ _ _ _ i.toTopos.pushforward
      i.toTopos.adjunction.rightAdjoint_preservesLimits⟩
  pushforward := i.toTopos.pushforward.inv
  adjunction := i.toTopos.pushforward.asEquivalence.toAdjunction

set_option maxHeartbeats 1600000 in
private def unitIso : 𝟭 (Sheaf Y.siteTopology (Type w)) ≅
    i.toTopos.inverseImage ⋙ i.toTopos.pushforward :=
  @asIso _ _ _ _ i.toTopos.adjunction.unit (by
    apply NatIso.isIso_of_isIso_app)

set_option maxHeartbeats 1600000 in
private def counitIso : i.toTopos.pushforward ⋙ i.toTopos.inverseImage ≅
    𝟭 (Sheaf X.siteTopology (Type w)) :=
  @asIso _ _ _ _ i.toTopos.adjunction.counit
    (@Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _
      i.toTopos.adjunction (pushforwardEquivalence i).fullyFaithfulFunctor.full
      (pushforwardEquivalence i).fullyFaithfulFunctor.faithful)

set_option maxHeartbeats 1600000 in
private def ringImageEquivalence :
    Sheaf Y.siteTopology RingCat.{w} ≌ Sheaf X.siteTopology RingCat.{w} :=
  CategoryTheory.Equivalence.mk i.toTopos.ringInverseImage (inverseTopos i).ringInverseImage
    ((MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := Y.siteTopology)).symm ≪≫
      (MorphismOfTopoiIn.ringInverseImageNatIso
        (f := MorphismOfTopoiIn.id Y.siteTopology)
        (g := MorphismOfTopoiIn.comp i.toTopos (inverseTopos i))
        (unitIso i)) ≪≫
      MorphismOfTopoiIn.ringInverseImageCompIso i.toTopos (inverseTopos i))
    ((MorphismOfTopoiIn.ringInverseImageCompIso (inverseTopos i) i.toTopos).symm ≪≫
      MorphismOfTopoiIn.ringInverseImageNatIso
        (f := MorphismOfTopoiIn.comp (inverseTopos i) i.toTopos)
        (g := MorphismOfTopoiIn.id X.siteTopology)
        (counitIso i) ≪≫
      MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := X.siteTopology))

end InverseTopos

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


namespace FittingMap

set_option maxHeartbeats 1600000 in
/-- The underlying geometric morphism of the missing edge is obtained by inverting the
back upper thickening and composing with the diagonal and front upper morphism. -/
def underlyingTopos : MorphismOfTopoiIn JC1p JC2p :=
  MorphismOfTopoiIn.comp
    (MorphismOfTopoiIn.comp front.upper.toTopos Q.g.toTopos) (inverseTopos back.upper)

set_option maxHeartbeats 1600000 in
private def inverseImageSourceIso :
    (underlyingTopos Q).ringInverseImage.obj (ringSheaf JC1p OC1p) ≅
      (inverseTopos back.upper).ringInverseImage.obj
        (Q.g.toTopos.ringInverseImage.obj (front.upper.toTopos.ringInverseImage.obj
          (ringSheaf JC1p OC1p))) :=
  (MorphismOfTopoiIn.ringInverseImageCompIso
      (MorphismOfTopoiIn.comp front.upper.toTopos Q.g.toTopos)
      (inverseTopos back.upper)).app (ringSheaf JC1p OC1p) ≪≫
    (inverseTopos back.upper).ringInverseImage.mapIso
      ((MorphismOfTopoiIn.ringInverseImageCompIso front.upper.toTopos Q.g.toTopos).app
        (ringSheaf JC1p OC1p))

set_option maxHeartbeats 1600000 in
private def coefficientIso :
    back.upper.toTopos.ringInverseImage.obj
        ((underlyingTopos Q).ringInverseImage.obj (ringSheaf JC1p OC1p)) ≅
      ringSheaf JC2 (Q.g.toTopos.commRingInverseImage.obj (normalizedRing front.upper)) :=
  back.upper.toTopos.ringInverseImage.mapIso (inverseImageSourceIso Q) ≪≫
    (ringImageEquivalence back.upper).counitIso.app _ ≪≫
    (Q.g.toTopos.ringInverseImage.mapIso
      (front.upper.toTopos.commRingInverseImageForgetRingIso.app OC1p)).symm ≪≫
    (Q.g.toTopos.commRingInverseImageForgetRingIso.app (normalizedRing front.upper)).symm

set_option maxHeartbeats 1600000 in
private def normalizeStructureMap
    (m : (underlyingTopos Q).ringInverseImage.obj (ringSheaf JC1p OC1p) ⟶
      ringSheaf JC2p OC2p) :
    Q.g.toTopos.commRingInverseImage.obj (normalizedRing front.upper) ⟶
      normalizedRing back.upper :=
  (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing (J := JC2)).preimage
    ((coefficientIso Q).inv ≫ back.upper.toTopos.ringInverseImage.map m ≫
      back.upper.toTopos.commRingInverseImageForgetRingIso.inv.app OC2p)

set_option maxHeartbeats 1600000 in
private def reconstructStructureMap
    (m : Q.g.toTopos.commRingInverseImage.obj (normalizedRing front.upper) ⟶
      normalizedRing back.upper) :
    (underlyingTopos Q).ringInverseImage.obj (ringSheaf JC1p OC1p) ⟶
      ringSheaf JC2p OC2p :=
  (ringImageEquivalence back.upper).fullyFaithfulFunctor.preimage
    ((coefficientIso Q).hom ≫ ringSheafMap m ≫
      back.upper.toTopos.commRingInverseImageForgetRingIso.hom.app OC2p)

set_option maxHeartbeats 1600000 in
private def leftFaceNatIso :
    back.upper.toTopos.pushforward ⋙ (underlyingTopos Q).pushforward ≅
      Q.g.toTopos.pushforward ⋙ front.upper.toTopos.pushforward :=
  (Functor.associator back.upper.toTopos.pushforward
      (pushforwardEquivalence back.upper).inverse
      (Q.g.toTopos.pushforward ⋙ front.upper.toTopos.pushforward)).symm ≪≫
    Functor.isoWhiskerRight (pushforwardEquivalence back.upper).unitIso.symm
      (Q.g.toTopos.pushforward ⋙ front.upper.toTopos.pushforward) ≪≫
    Functor.leftUnitor _

set_option maxHeartbeats 1600000 in
private def rightFaceNatIso :
    (underlyingTopos Q).pushforward ⋙ front.right.toTopos.pushforward ≅
      back.right.toTopos.pushforward ⋙ Q.base'.toTopos.pushforward :=
  (CategoryTheory.Equivalence.congrLeft (E := Sheaf JB1p (Type w))
      (pushforwardEquivalence back.upper)).fullyFaithfulInverse.preimageIso
    ((Functor.associator back.upper.toTopos.pushforward (underlyingTopos Q).pushforward
        front.right.toTopos.pushforward).symm ≪≫
      Functor.isoWhiskerRight (leftFaceNatIso Q) front.right.toTopos.pushforward ≪≫
      Functor.associator Q.g.toTopos.pushforward front.upper.toTopos.pushforward
        front.right.toTopos.pushforward ≪≫
      Functor.isoWhiskerLeft Q.g.toTopos.pushforward front.cell.homIso ≪≫
      (Functor.associator Q.g.toTopos.pushforward front.left.toTopos.pushforward
        front.lower.toTopos.pushforward).symm ≪≫
      Functor.isoWhiskerRight Q.leftCell.homIso front.lower.toTopos.pushforward ≪≫
      Functor.associator back.left.toTopos.pushforward Q.base.toTopos.pushforward
        front.lower.toTopos.pushforward ≪≫
      Functor.isoWhiskerLeft back.left.toTopos.pushforward Q.lowerCell.homIso.symm ≪≫
      (Functor.associator back.left.toTopos.pushforward back.lower.toTopos.pushforward
        Q.base'.toTopos.pushforward).symm ≪≫
      Functor.isoWhiskerRight back.cell.homIso.symm Q.base'.toTopos.pushforward ≪≫
      Functor.associator back.upper.toTopos.pushforward back.right.toTopos.pushforward
        Q.base'.toTopos.pushforward)

end FittingMap

set_option maxHeartbeats 1600000 in
/-- A compatible missing ringed-topos morphism has the canonical underlying geometric
morphism and a structure map whose inverse image fills the relative square-zero diagram. -/
structure FittingMap (D : RelativeDiagram Q) where
  /-- The structure-sheaf map over the canonical underlying geometric morphism. -/
  structureMap : (FittingMap.underlyingTopos Q).ringInverseImage.obj (ringSheaf JC1p OC1p) ⟶
    ringSheaf JC2p OC2p
  /-- The transported structure map fits both faces and induces the prescribed kernel map. -/
  fits : FirstOrderThickening.RelativeDiagram.Fits (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q)
    (FittingMap.normalizeStructureMap Q structureMap)

namespace FittingMap

variable {Q}

set_option maxHeartbeats 1600000 in
/-- A fitting structure map determines a genuine morphism of ringed topoi. -/
def hom {D : RelativeDiagram Q} (φ : FittingMap Q D) :
    ToposHom (ofCommRingSheaf JC2p OC2p) (ofCommRingSheaf JC1p OC1p) where
  toTopos := underlyingTopos Q
  structureMap := φ.structureMap

set_option maxHeartbeats 1600000 in
/-- The normalized face equations imply compatibility of the canonical comparison cells
with the two structure-sheaf maps of a geometric filler. -/
private theorem toNormalized_laws {D : RelativeDiagram Q} (φ : FittingMap Q D) :
    ((back.upper.comp φ.hom).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans
        (f := (back.upper.comp φ.hom).toTopos)
        (g := (Q.g.comp front.upper).toTopos)
        (leftFaceNatIso Q).hom).app (ringSheaf JC2 OC2) =
      (Q.g.comp front.upper).directStructureMap) ∧
    ((φ.hom.comp front.right).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans
        (f := (φ.hom.comp front.right).toTopos)
        (g := (back.right.comp Q.base').toTopos)
        (rightFaceNatIso Q).hom).app (ringSheaf JC2p OC2p) =
      (back.right.comp Q.base').directStructureMap) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- The canonical left comparison makes a filler compatible with the two upper thickenings. -/
def leftCell {D : RelativeDiagram Q} (φ : FittingMap Q D) :
    TwoIso (back.upper.comp φ.hom) (Q.g.comp front.upper) where
  homIso := leftFaceNatIso Q
  comm := (toNormalized_laws φ).1

set_option maxHeartbeats 1600000 in
/-- The canonical right comparison makes a filler compatible with the two right structure maps. -/
def rightCell {D : RelativeDiagram Q} (φ : FittingMap Q D) :
    TwoIso (φ.hom.comp front.right) (back.right.comp Q.base') where
  homIso := rightFaceNatIso Q
  comm := (toNormalized_laws φ).2

set_option maxHeartbeats 1600000 in
/-- Inverse image of a compatible geometric filler gives its fitting ring-sheaf map. -/
def toNormalized {D : RelativeDiagram Q} (φ : FittingMap Q D) :
    FirstOrderThickening.FittingMap (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q) :=
  FirstOrderThickening.FittingMap.of (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (normalizeStructureMap Q φ.structureMap)
    φ.fits.1 φ.fits.2.1 (φ.fits.2.2 φ.fits.1)

set_option maxHeartbeats 1600000 in
/-- Reconstructing a fitting ring-sheaf map along the thickening equivalence preserves
its compatibility with the two faces and the prescribed kernel map. -/
private theorem reconstruct_laws (D : RelativeDiagram Q)
    (φ : FirstOrderThickening.FittingMap (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q)) :
    FirstOrderThickening.RelativeDiagram.Fits (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q)
      (normalizeStructureMap Q (reconstructStructureMap Q (FirstOrderThickening.FittingMap.hom (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) φ))) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- A fitting ring-sheaf map reconstructs a geometric filler by the thickening equivalence. -/
def ofNormalized {D : RelativeDiagram Q}
    (φ : FirstOrderThickening.FittingMap (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q)) : FittingMap Q D where
  structureMap := reconstructStructureMap Q (FirstOrderThickening.FittingMap.hom (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) φ)
  fits := reconstruct_laws D φ

set_option maxHeartbeats 1600000 in
/-- Normalization and reconstruction are mutually inverse on compatible fillers. -/
private theorem normalizedEquiv_laws (D : RelativeDiagram Q) :
    (∀ φ : FittingMap Q D, ofNormalized (toNormalized φ) = φ) ∧
      (∀ φ : FirstOrderThickening.FittingMap (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q),
        toNormalized (ofNormalized φ) = φ) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- Geometric fillers correspond canonically to fitting maps of the inverse-image diagram. -/
def normalizedEquiv (D : RelativeDiagram Q) :
    FittingMap Q D ≃ FirstOrderThickening.FittingMap (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D) (D.normalizedDiagram Q) where
  toFun := toNormalized
  invFun := ofNormalized
  left_inv := (normalizedEquiv_laws D).1
  right_inv := (normalizedEquiv_laws D).2

set_option maxHeartbeats 1600000 in
private def differentialCarrier :
    (sheafCompose JC1 (forget RingCat.{w})).obj (ringSheaf JC1 OC1) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf JC1 OC1)).obj
        Ω(normalizedProjection front.left) where
  hom :=
    { app := fun U ↦ ↾fun x ↦ (relativeDifferential (normalizedProjection front.left)).d x
      naturality := by
        intro U V f
        ext x
        exact (relativeDifferential (normalizedProjection front.left)).d_map f x }

set_option maxHeartbeats 1600000 in
private def perturbCarrier
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) :
    (sheafCompose JC2 (forget RingCat.{w})).obj (ringSheaf JC2 (normalizedRing Q.g)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf JC2 (normalizedRing Q.g))).obj
        ((restrictionAlong (normalizedProjection Q.g)).obj
          (FirstOrderThickening.ideal (normalizedProjection back.upper)
            (hπ := normalizedProjection_isFirstOrderThickening back.upper))) :=
  (sheafCompose JC2 (forget RingCat.{w})).map
      (Q.g.toTopos.commRingInverseImageForgetRingIso.hom.app OC1) ≫
    Q.g.toTopos.ringInverseImageForgetIso.hom.app (ringSheaf JC1 OC1) ≫
    (Q.g.toTopos.adjunction.homEquiv _ _).symm
      (differentialCarrier (front := front) ≫
        (Sheaf.InternalModule.ToInternal.underlying (ringSheaf JC1 OC1)).map α ≫
        (ModulePushforward.forgetIso Q.g).hom.app (idealModule back.upper)) ≫
    (Sheaf.InternalModule.ToInternal.underlying (ringSheaf JC2 OC2)).map
      (normalizedIdealIso back.upper).inv

set_option maxHeartbeats 1600000 in
private def perturbConditions
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) : Prop :=
  let M := (restrictionAlong (normalizedProjection Q.g)).obj
    (FirstOrderThickening.ideal (normalizedProjection back.upper)
      (hπ := normalizedProjection_isFirstOrderThickening back.upper))
  let d : ∀ U : C2ᵒᵖ, (normalizedRing Q.g).obj.obj U → M.val.obj U :=
    fun U x ↦ (perturbCarrier (Q := Q) α).hom.app U x
  (∀ U x y, d U (x + y) = d U x + d U y) ∧
  (∀ U x y, d U (x * y) = x • d U y + y • d U x) ∧
  (∀ U (a : (Q.g.toTopos.commRingInverseImage.obj (normalizedRing front.left)).obj.obj U),
    d U ((Q.g.toTopos.commRingInverseImage.map
      (normalizedProjection front.left)).hom.app U a) = 0) ∧
  (∀ {U V : C2ᵒᵖ} (i : U ⟶ V) (x : (normalizedRing Q.g).obj.obj U),
    d V ((normalizedRing Q.g).obj.map i x) = M.val.map i (d U x))

set_option maxHeartbeats 1600000 in
private def normalizedPerturbation
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper))
    (h : perturbConditions (Q := Q) α) :
    Ω(Q.g.toTopos.commRingInverseImage.map (normalizedProjection front.left)) ⟶
      (restrictionAlong (normalizedProjection Q.g)).obj
        (FirstOrderThickening.ideal (normalizedProjection back.upper)
          (hπ := normalizedProjection_isFirstOrderThickening back.upper)) :=
  relativeDifferentialDesc _
    (PresheafOfModules.Derivation'.mk
      (fun U ↦ ModuleCat.Derivation.mk
        (fun x ↦ (perturbCarrier (Q := Q) α).hom.app U x)
        (h.1 U) (h.2.1 U) (h.2.2.1 U))
      (fun _ _ i x ↦ h.2.2.2 i x))

set_option maxHeartbeats 1600000 in
private def perturbWithProof (D : RelativeDiagram Q)
    (h : ∀ α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper), perturbConditions (Q := Q) α)
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) (φ : FittingMap Q D) : FittingMap Q D :=
  ofNormalized (FirstOrderThickening.perturb (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D)
    (D := D.normalizedDiagram Q) (normalizedPerturbation α (h α)) (toNormalized φ))

set_option maxHeartbeats 1600000 in
/-- The transported universal derivation is relative to the inverse-image base, and its
perturbations have identity at zero and compose by addition. -/
private theorem perturb_laws (D : RelativeDiagram Q) :
    (∀ α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper), perturbConditions (Q := Q) α) ∧
    (∀ (h : ∀ α : Ω(normalizedProjection front.left) ⟶
        Q.g.modulePushforward.obj (idealModule back.upper), perturbConditions (Q := Q) α)
      (φ : FittingMap Q D)
      (α β : Ω(normalizedProjection front.left) ⟶
        Q.g.modulePushforward.obj (idealModule back.upper)),
      perturbWithProof D h 0 φ = φ ∧
        perturbWithProof D h α (perturbWithProof D h β φ) =
          perturbWithProof D h (α + β) φ) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- A morphism from front relative differentials to the direct image of the back kernel
acts on geometric fillers by adding its transported kernel-valued derivation. -/
def perturb {D : RelativeDiagram Q}
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) (φ : FittingMap Q D) : FittingMap Q D :=
  perturbWithProof D (perturb_laws D).1 α φ

set_option maxHeartbeats 1600000 in
/-- Zero acts trivially on a geometric filler, and successive perturbations add. -/
theorem perturb_zero_add {D : RelativeDiagram Q} (φ : FittingMap Q D)
    (α β : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) :
    perturb 0 φ = φ ∧ perturb α (perturb β φ) = perturb (α + β) φ :=
  (perturb_laws D).2 (perturb_laws D).1 φ α β

end FittingMap

end RingedSite.ToposHom.Thickening
