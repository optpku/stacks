/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FittingMap
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.MapObstruction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.CellModel
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.NaiveCotangent.InverseImage
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Embedding.TruncGE
public import ReasLib.CategoryTheory.DerivedCategory.Functor.CellModel
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Category.Ring.Colimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open SheafOfModules.RingedSite
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

set_option backward.privateInPublic true

universe w

namespace RingedSite.ToposHom.Thickening


namespace MapObstructionConstruction

section Truncation

variable {E : Type*} [Category* E] [Abelian E] [HasDerivedCategory E]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev lowerComplex (n : ℤ) : CochainComplex E ℤ ⥤ CochainComplex E ℤ :=
  ComplexShape.Embedding.truncGEFunctor (embeddingUpIntGE n) E

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem lowerInverts (n : ℤ) :
    (HomologicalComplex.quasiIso E (up ℤ)).IsInvertedBy
      (lowerComplex n ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have h : QuasiIso f := hf
  have ht : QuasiIso (CochainComplex.truncGEMap f n) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro i _
    exact h.quasiIsoAt i
  exact Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso E (up ℤ)) _ ht

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def lowerDerived (n : ℤ) : DerivedCategory E ⥤ DerivedCategory E :=
  Localization.lift (lowerComplex n ⋙ DerivedCategory.Q) (lowerInverts n) DerivedCategory.Q

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def lowerFac (n : ℤ) : DerivedCategory.Q ⋙ lowerDerived (E := E) n ≅ lowerComplex n ⋙ DerivedCategory.Q :=
  Localization.fac (lowerComplex n ⋙ DerivedCategory.Q) (lowerInverts n) DerivedCategory.Q

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def lowerHom (n : ℤ) {K L : CochainComplex E ℤ}
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj (K.truncGE n) ⟶ DerivedCategory.Q.obj (L.truncGE n) :=
  (lowerFac n).inv.app K ≫ (lowerDerived n).map f ≫ (lowerFac n).hom.app L

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def descendLow {A U L : CochainComplex E ℤ} (n : ℤ) (f : A ⟶ U)
    (hf : QuasiIso (CochainComplex.truncGEMap f n)) (hL : L.IsGE n)
    (m : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj L :=
  DerivedCategory.Q.map (U.πTruncGE n) ≫
    (Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso E (up ℤ))
      (CochainComplex.truncGEMap f n) hf).inv ≫ lowerHom n m ≫
    (Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso E (up ℤ))
      (L.πTruncGE n) ((CochainComplex.quasiIso_πTruncGE_iff L n).mpr hL)).inv

end Truncation

private theorem binarySheafColimits {E : Type*} [Category* E]
    (J : GrothendieckTopology E) [HasWeakSheafify J CommRingCat.{w}] :
    HasColimitsOfShape (Discrete WalkingPair) (Sheaf J CommRingCat.{w}) :=
  @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ J CommRingCat.{w} _
    (Discrete WalkingPair) _ inferInstance
    (by infer_instance)



end MapObstructionConstruction

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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The naive cotangent complex of the front left morphism is the canonical complex
of its inverse-image structure-ring map. -/
def frontNaiveCotangent : CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ :=
  NaiveCotangent.obj (normalizedRing front.left) (Under.mk (normalizedProjection front.left))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The derived inverse image of the front naive cotangent complex along the diagonal. -/
def pulledNaiveCotangent :=
  (NativeDerived.CellPullback.functor Q.g).obj
    ((NativeDerived.CellPullback.Q JC1 OC1).obj (frontNaiveCotangent (front := front)))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The kernel module of the back upper thickening, concentrated in degree zero. -/
def kernelSingle :=
  (NativeDerived.CellPullback.Q JC2 OC2).obj
    ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
      (idealModule back.upper))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Pullback and direct image give the additive identification between the two
relative-differential Hom groups. -/
def homOmegaPushforwardEquiv :
    (Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) ≃+
    (Q.g.modulePullback.obj Ω(normalizedProjection front.left) ⟶
      idealModule back.upper) :=
  (@Adjunction.homAddEquiv _ _ _ _ _ _ _ _ Q.g.moduleAdjunction
    (modulePullback_additive Q.g) Ω(normalizedProjection front.left)
      (idealModule back.upper)).symm

namespace MapObstructionConstruction

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev omegaSingle :=
  HomologicalComplex.single (SheafOfModules (ringSheaf JC1 OC1)) (up ℤ) 0

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def homOmegaDerived
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) :
    pulledNaiveCotangent Q ⟶ kernelSingle (back := back) :=
  (NativeDerived.CellPullback.functor Q.g).map
      ((NativeDerived.CellPullback.Q JC1 OC1).map
        (NaiveCotangent.augmentation (normalizedRing front.left)
          (Under.mk (normalizedProjection front.left)))) ≫
    (NativeDerived.CellPullback.counit Q.g).app
      (omegaSingle.obj Ω(normalizedProjection front.left)) ≫
    (NativeDerived.CellPullback.Q JC2 OC2).map
      ((@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
          Q.g.modulePullback
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ Q.g.modulePullback
            (modulePullback_additive Q.g)) (up ℤ) inferInstance (0 : ℤ)).hom.app Ω(normalizedProjection front.left) ≫
        (CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).map
          (homOmegaPushforwardEquiv Q α))

end MapObstructionConstruction

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A relative-differential Hom element gives its canonical degree-zero Ext class
by the cotangent augmentation and the module adjunction. -/
def homOmegaExtZero
    (α : Ω(normalizedProjection front.left) ⟶
      Q.g.modulePushforward.obj (idealModule back.upper)) :
    Ext⁽(0 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back)) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    (MapObstructionConstruction.homOmegaDerived Q α)

namespace MapObstructionConstruction

variable [UnivLE.{max uC2 vC2, w}]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev normalizedCotangent :=
  NaiveCotangent.obj (Q.g.toTopos.commRingInverseImage.obj (normalizedRing front.left))
    (Under.mk (Q.g.toTopos.commRingInverseImage.map (normalizedProjection front.left)))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev scalarFunctor := (sameSiteHom (normalizedProjection Q.g)).modulePullback

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev scalarComplex :=
  ((scalarFunctor Q).mapHomologicalComplex (up ℤ)).obj
    (SheafOfModules.CellReplacement.model (normalizedCotangent Q))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev underivedComplex :=
  (extendComplex (normalizedProjection Q.g)).obj (normalizedCotangent Q)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def lowDegreeComparison :
    (NativeDerived.CellPullback.cochain Q.g).obj (frontNaiveCotangent (front := front)) ⟶
      underivedComplex Q :=
  Q.g.modulePullbackComplex.map
      (SheafOfModules.CellReplacement.augmentation (frontNaiveCotangent (front := front))) ≫
    RingedSite.ToposHom.NaiveCotangent.underivedComparison (hcolC := binarySheafColimits JC1) (hcolD := binarySheafColimits JC2)
      Q.g (normalizedProjection front.left)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def scalarComparison : scalarComplex Q ⟶ underivedComplex Q :=
  ((scalarFunctor Q).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation (normalizedCotangent Q)) ≫
    (pullbackComplexExtendIso (normalizedProjection Q.g)).hom.app (normalizedCotangent Q)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def LowDegreeLaws : Prop :=
  QuasiIso (CochainComplex.truncGEMap (lowDegreeComparison Q) (-1)) ∧
  QuasiIso (CochainComplex.truncGEMap (scalarComparison Q) (-1)) ∧
  (HomologicalComplex.quasiIso (SheafOfModules (ringSheaf JC2 (normalizedRing Q.g)))
    (up ℤ)).IsInvertedBy (Functor.CellModel.cochain (scalarFunctor Q)) ∧
  (∀ K, QuasiIso (((scalarFunctor Q).mapHomologicalComplex (up ℤ)).map
    (SheafOfModules.CellReplacement.augmentation (SheafOfModules.CellReplacement.model K))))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The derived comparison to the ordinary cotangent model is a quasi-isomorphism
after good truncation in degrees at least minus one. -/
private theorem lowDegreeComparison_quasiIso : LowDegreeLaws Q := sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def scalarModel : Functor.LeftDerived.Model
    (Functor.CellModel.ordinaryCochain (scalarFunctor Q)) DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules (ringSheaf JC2 (normalizedRing Q.g)))
        (up ℤ)) :=
  ⟨Functor.CellModel.derived (scalarFunctor Q) (lowDegreeComparison_quasiIso Q).2.2.1,
    Functor.CellModel.counit (scalarFunctor Q) (lowDegreeComparison_quasiIso Q).2.2.1,
    Functor.CellModel.isLeftDerived (scalarFunctor Q)
      (lowDegreeComparison_quasiIso Q).2.2.1
      (fun K ↦ Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (up ℤ)) _
        ((lowDegreeComparison_quasiIso Q).2.2.2 K))⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def selectedScalarModel : Functor.LeftDerived.Model
    (Functor.CellModel.ordinaryCochain (scalarFunctor Q)) DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules (ringSheaf JC2 (normalizedRing Q.g)))
        (up ℤ)) :=
  ⟨SheafOfModules.RingedSite.SameSite.pullbackDerived (normalizedProjection Q.g),
    (@Functor.LeftDerived.Homotopy.cochainCounit _ _ _ _ _ _ _ _
      (scalarFunctor Q) _
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived
        (sameSiteHom (normalizedProjection Q.g)))),
    (@Functor.LeftDerived.Homotopy.cochainIsLeftDerived _ _ _ _ _ _ _ _
      (scalarFunctor Q) _
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived
        (sameSiteHom (normalizedProjection Q.g))))⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def scalarCellIso :
    (SheafOfModules.RingedSite.SameSite.pullbackDerived (normalizedProjection Q.g)).obj
        (DerivedCategory.Q.obj (normalizedCotangent Q)) ≅
      DerivedCategory.Q.obj (scalarComplex Q) :=
  ((selectedScalarModel Q).iso (scalarModel Q)).app
      (DerivedCategory.Q.obj (normalizedCotangent Q)) ≪≫
    (Functor.CellModel.fac (scalarFunctor Q)
      (lowDegreeComparison_quasiIso Q).2.2.1).app (normalizedCotangent Q)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def geometricCellIso : pulledNaiveCotangent Q ≅
    DerivedCategory.Q.obj
      ((NativeDerived.CellPullback.cochain Q.g).obj (frontNaiveCotangent (front := front))) :=
  (NativeDerived.CellPullback.computation Q.g).app (frontNaiveCotangent (front := front))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev geometricSingle (i : ℤ) :=
  (CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) (-i)).obj
    (idealModule back.upper)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def geometricShiftIso (i : ℤ) :
    (kernelSingle (back := back))⟦i⟧ ≅ DerivedCategory.Q.obj (geometricSingle (back := back) i) :=
  ((DerivedCategory.singleFunctors (SheafOfModules (ringSheaf JC2 OC2))).shiftIso i (-i) 0
    (add_neg_cancel i)).app (idealModule back.upper)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def commonSingleIso (i : ℤ) :
    DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) (-i)).obj
          (FirstOrderThickening.ideal (normalizedProjection back.upper)
            (hπ := normalizedProjection_isFirstOrderThickening back.upper))) ≅
      DerivedCategory.Q.obj (geometricSingle (back := back) i) :=
  DerivedCategory.Q.mapIso
    ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) (-i)).mapIso
      (normalizedIdealIso back.upper))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem geometricSingle_isGE (i : ℤ) (hi : i = 0 ∨ i = 1) :
    (geometricSingle (back := back) i).IsGE (-1) := by
  rcases hi with rfl | rfl
  · change ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
      (idealModule back.upper)).IsGE (-1)
    exact CochainComplex.isGE_of_ge _ (-1) 0 (by omega)
  · infer_instance

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def extToCommon (i : ℤ) (hi : i = 0 ∨ i = 1)
    (e : Ext⁽i⁾(pulledNaiveCotangent Q, kernelSingle (back := back))) :
    Ext⁽i⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (normalizedProjection Q.g)).obj
      (DerivedCategory.Q.obj (normalizedCotangent Q)),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
          (FirstOrderThickening.ideal (normalizedProjection back.upper)
            (hπ := normalizedProjection_isFirstOrderThickening back.upper)))) :=
  (scalarCellIso Q).hom ≫ DerivedCategory.Q.map (scalarComparison Q) ≫
    descendLow (-1) (lowDegreeComparison Q) (lowDegreeComparison_quasiIso Q).1
      (geometricSingle_isGE (back := back) i hi)
      ((geometricCellIso Q).inv ≫ e ≫ (geometricShiftIso (back := back) i).hom) ≫
    (commonSingleIso (back := back) i).inv ≫
    ((DerivedCategory.singleFunctors (SheafOfModules (ringSheaf JC2 OC2))).shiftIso i (-i) 0
      (add_neg_cancel i)).inv.app _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def extFromCommon (i : ℤ) (hi : i = 0 ∨ i = 1)
    (e : Ext⁽i⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (normalizedProjection Q.g)).obj
      (DerivedCategory.Q.obj (normalizedCotangent Q)),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
          (FirstOrderThickening.ideal (normalizedProjection back.upper)
            (hπ := normalizedProjection_isFirstOrderThickening back.upper))))) :
    Ext⁽i⁾(pulledNaiveCotangent Q, kernelSingle (back := back)) :=
  (geometricCellIso Q).hom ≫ DerivedCategory.Q.map (lowDegreeComparison Q) ≫
    descendLow (-1) (scalarComparison Q) (lowDegreeComparison_quasiIso Q).2.1
      (geometricSingle_isGE (back := back) i hi)
      ((scalarCellIso Q).inv ≫ e ≫
        ((DerivedCategory.singleFunctors (SheafOfModules (ringSheaf JC2 OC2))).shiftIso i (-i) 0
          (add_neg_cancel i)).hom.app _ ≫ (commonSingleIso (back := back) i).hom) ≫
    (geometricShiftIso (back := back) i).inv

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def ExtComparisonLaws : Prop :=
  (∀ i hi e, extFromCommon Q i hi (extToCommon Q i hi e) = e) ∧
  (∀ i hi e, extToCommon Q i hi (extFromCommon Q i hi e) = e) ∧
  (∀ i hi e e', extToCommon Q i hi (e + e') = extToCommon Q i hi e + extToCommon Q i hi e')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The truncation and localization maps give inverse additive comparisons on Ext
in degrees zero and one. -/
private theorem extComparison_laws : ExtComparisonLaws Q := sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def extComparison (i : ℤ) (hi : i = 0 ∨ i = 1) :
    Ext⁽i⁾(pulledNaiveCotangent Q, kernelSingle (back := back)) ≃+
      Ext⁽i⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (normalizedProjection Q.g)).obj
        (DerivedCategory.Q.obj (normalizedCotangent Q)),
        DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
            (FirstOrderThickening.ideal (normalizedProjection back.upper)
              (hπ := normalizedProjection_isFirstOrderThickening back.upper)))) where
  toFun := extToCommon Q i hi
  invFun := extFromCommon Q i hi
  left_inv := (extComparison_laws Q).1 i hi
  right_inv := (extComparison_laws Q).2.1 i hi
  map_add' := (extComparison_laws Q).2.2 i hi

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def extOneComparison := extComparison Q 1 (Or.inr rfl)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def extZeroComparison := extComparison Q 0 (Or.inl rfl)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private abbrev pulledOmegaSingle :=
  (CochainComplex.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).obj
    (Q.g.modulePullback.obj Ω(normalizedProjection front.left))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def omegaCellMap :
    (NativeDerived.CellPullback.cochain Q.g).obj (frontNaiveCotangent (front := front)) ⟶
      pulledOmegaSingle Q :=
  Q.g.modulePullbackComplex.map
      (SheafOfModules.CellReplacement.augmentation (frontNaiveCotangent (front := front)) ≫
        NaiveCotangent.augmentation (normalizedRing front.left)
          (Under.mk (normalizedProjection front.left))) ≫
    (@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
      Q.g.modulePullback
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ Q.g.modulePullback
        (modulePullback_additive Q.g)) (up ℤ) inferInstance (0 : ℤ)).hom.app _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def homOmegaExtZeroInverse
    (h : QuasiIso (CochainComplex.truncGEMap (omegaCellMap Q) 0))
    (e : Ext⁽(0 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back))) :
    Ω(normalizedProjection front.left) ⟶ Q.g.modulePushforward.obj (idealModule back.upper) :=
  (homOmegaPushforwardEquiv Q).symm
    ((DerivedCategory.singleFunctor (SheafOfModules (ringSheaf JC2 OC2)) 0).preimage
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules (ringSheaf JC2 OC2)) 0).hom.app _ ≫
        descendLow 0 (omegaCellMap Q) h (by infer_instance)
          ((geometricCellIso Q).inv ≫ (CategoryTheory.ShiftedHom.homEquiv 0 rfl).symm e) ≫
        (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules (ringSheaf JC2 OC2)) 0).inv.app _))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private def HomOmegaExtZeroLaws : Prop :=
  QuasiIso (CochainComplex.truncGEMap (omegaCellMap Q) 0) ∧
  (∀ h α, homOmegaExtZeroInverse Q h (homOmegaExtZero Q α) = α) ∧
  (∀ h e, homOmegaExtZero Q (homOmegaExtZeroInverse Q h e) = e) ∧
  (∀ α β, homOmegaExtZero Q (α + β) = homOmegaExtZero Q α + homOmegaExtZero Q β)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The cotangent augmentation identifies degree-zero Ext with the
relative-differential Hom group by inverse additive maps. -/
private theorem homOmegaExtZero_laws : HomOmegaExtZeroLaws Q := sorry

end MapObstructionConstruction

variable [UnivLE.{max uC2 vC2, w}]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The relative-differential Hom group is canonically additively equivalent to
degree-zero Ext from the derived inverse image of the naive cotangent complex. -/
def homOmegaExtZeroEquiv :
    (Ω(normalizedProjection front.left) ⟶ Q.g.modulePushforward.obj (idealModule back.upper)) ≃+
      Ext⁽(0 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back)) where
  toFun := homOmegaExtZero Q
  invFun := MapObstructionConstruction.homOmegaExtZeroInverse Q
    (MapObstructionConstruction.homOmegaExtZero_laws Q).1
  left_inv := (MapObstructionConstruction.homOmegaExtZero_laws Q).2.1 _
  right_inv := (MapObstructionConstruction.homOmegaExtZero_laws Q).2.2.1 _
  map_add' := (MapObstructionConstruction.homOmegaExtZero_laws Q).2.2.2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The obstruction to filling an open cube of first-order thickenings is the
normalized relative ring-map obstruction transported to the geometric Ext group. -/
def mapObstruction (D : RelativeDiagram Q) :
    Ext⁽(1 : ℤ)⁾(pulledNaiveCotangent Q, kernelSingle (back := back)) :=
  (MapObstructionConstruction.extOneComparison Q).symm
    (FirstOrderThickening.mapObstruction
      (hπO1 := RelativeDiagram.normalizedFrontUpper_isFirstOrderThickening Q D)
      (hπB1 := RelativeDiagram.normalizedFrontLower_isFirstOrderThickening Q D)
      (hπO2 := normalizedProjection_isFirstOrderThickening back.upper)
      (hπB2 := RelativeDiagram.normalizedBackLower_isFirstOrderThickening Q D)
      (RelativeDiagram.normalizedDiagram Q D))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical degree-one obstruction vanishes exactly when there is a
compatible missing ringed-topos morphism inducing the prescribed kernel map. -/
theorem mapObstruction_eq_zero_iff (D : RelativeDiagram Q) :
    mapObstruction Q D = 0 ↔ Nonempty (FittingMap Q D) := sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Any two compatible fillers differ by a unique relative-differential Hom element
under the canonical perturbation operation. -/
theorem fittingMap_principalHomogeneous (D : RelativeDiagram Q)
    (φ φ' : FittingMap Q D) :
    ∃! α : Ω(normalizedProjection front.left) ⟶ Q.g.modulePushforward.obj (idealModule back.upper),
      FittingMap.perturb α φ = φ' := sorry

end RingedSite.ToposHom.Thickening
