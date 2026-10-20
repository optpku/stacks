/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.IdealHom
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction.Naturality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Same-site normalization and existence obstructions of ringed-topos thickenings -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite
open SheafOfModules.ChangeOfRings
open CategoryTheory.Abelian (Ext)

noncomputable section

universe uC vC uD vD uE vE wExt

namespace RingedSite.ToposHom.Thickening

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JD.HasSheafCompose (forget RingCat.{max uC vC})]
variable {O : Sheaf JC CommRingCat.{max uC vC}}
variable {O' : Sheaf JD CommRingCat.{max uC vC}}

/-- The thickened structure ring transported to the site of the unthickened topos. -/
def normalizedRing (i : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD O')) :
    Sheaf JC CommRingCat.{max uC vC} :=
  i.toTopos.commRingInverseImage.obj O'

/-- The normalized projection is the inverse-image structure map transported through
the genuine comparison between commutative-ring and ring inverse image. -/
def normalizedProjection (i : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD O')) :
    normalizedRing i ⟶ O :=
  (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing (J := JC)).preimage
    ((i.toTopos.commRingInverseImageForgetRingIso).hom.app O' ≫ i.structureMap)

variable [JC.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JD.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [HasSheafify JD AddCommGrpCat.{max uC vC}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasWeakSheafify JC CommRingCat.{max uC vC}]
variable [JC.WEqualsLocallyBijective CommRingCat.{max uC vC}]
variable [HasWeakSheafify JC AddCommGrpCat.{max uC vC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable (i : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD O'))
variable [IsFirstOrderThickening i]

/-- Normalizing a first-order thickening gives a locally surjective square-zero
projection on the unthickened site. -/
theorem normalizedProjection_isFirstOrderThickening :
    SheafOfModules.RingedSite.IsFirstOrderThickening (normalizedProjection i) := by
  sorry

variable [(SheafOfModules.restrictScalars.{max uC vC} i.structureMap).IsRightAdjoint]

/-- The normalized square-zero ideal and the inverse-image ideal are identified by
kernel transport and the extension-restriction adjunction. -/
def normalizedIdealIso :
    FirstOrderThickening.ideal (normalizedProjection i)
      (hπ := normalizedProjection_isFirstOrderThickening i) ≅
      idealModule i := by
  let hπ := normalizedProjection_isFirstOrderThickening i
  let π := normalizedProjection i
  let R := i.toTopos.ringInverseImage.obj (ringSheaf JD O')
  let L := (i.toTopos.moduleInverseImage (ringSheaf JD O')).obj (ker i)
  let M := FirstOrderThickening.ideal π (hπ := hπ)
  let e := i.toTopos.commRingInverseImageForgetRingIso.app O'
  let F := ToInternal.underlying (ringSheaf JD O')
  let G := i.toTopos.inverseImage
  have forgetComposite : PreservesFiniteLimits
      (sheafCompose JD (forget AddCommGrpCat.{max uC vC}) ⋙
        sheafToPresheaf JD (Type (max uC vC))) := by
    change PreservesFiniteLimits
      (sheafToPresheaf JD AddCommGrpCat.{max uC vC} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{max uC vC}))
    infer_instance
  have forgetful : PreservesFiniteLimits
      (sheafCompose JD (forget AddCommGrpCat.{max uC vC})) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have preserveF : PreservesFiniteLimits F := comp_preservesFiniteLimits
    (SheafOfModules.toSheaf _) (sheafCompose JD (forget AddCommGrpCat.{max uC vC}))
  have preserveFG : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  let g := kernelMap i
  have preserve : PreservesLimit (parallelPair g 0) (F ⋙ G) :=
    @PreservesLimitsOfShape.preservesLimit _ _ _ _ _ _ (F ⋙ G)
      (preserveFG.preservesFiniteLimits WalkingParallelPair) (parallelPair g 0)
  let kernelComparison := @PreservesEqualizer.iso _ _ _ _ (F ⋙ G) _ _ g 0
    inferInstance inferInstance preserve
  let underlyingL := (i.toTopos.moduleInverseImageForgetIso (ringSheaf JD O')).app (ker i)
  let unitComparison : G.obj (F.obj (SheafOfModules.unit (ringSheaf JD O'))) ≅
      (ToInternal.underlying R).obj (SheafOfModules.unit R) :=
    (i.toTopos.ringInverseImageForgetIso.app (ringSheaf JD O')).symm
  let inclusionL := underlyingL.hom ≫ G.map (F.map (kernelIdeal_ι i)) ≫ unitComparison.hom
  let inclusionM :=
    (ToInternal.underlying (ringSheaf JC (normalizedRing i))).map
      ((FirstOrderThickening.ideal_forgetIso π (hπ := hπ)).hom ≫ KernelIdeal.ι π)
  let ringCarrierMap := (sheafCompose JC (forget RingCat.{max uC vC})).map e.hom
  let ringCarrierInv := (sheafCompose JC (forget RingCat.{max uC vC})).map e.inv
  let toAmbientUnit := inclusionM ≫ ringCarrierMap ≫ unitComparison.inv
  let toNormalizedUnit := inclusionL ≫ ringCarrierInv
  let conditions : Prop :=
    (toAmbientUnit ≫ (F ⋙ G).map g =
      toAmbientUnit ≫ (F ⋙ G).map (0 : _ ⟶ _)) ∧
    (∀ U (x : L.val.obj U),
      (π.hom.app U).hom ((toNormalizedUnit.hom.app U) x) = 0)
  let reverseCarrier (p : conditions) :=
    equalizer.lift toAmbientUnit p.1 ≫ kernelComparison.inv ≫ underlyingL.inv
  let scalarUnit := (extendRestrictAdjunction i.structureMap).unit.app L
  let reverseMap (p : conditions) :=
    reverseCarrier p ≫ (ToInternal.underlying R).map scalarUnit
  let forwardApp (p : conditions) (U : Cᵒᵖ) (x : L.val.obj U) : M.val.obj U :=
    (hπ.isSquareZero.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π)).inv.hom.app U
      ((KernelIdeal.sectionsIso π U).inv
        ⟨toNormalizedUnit.hom.app U x, p.2 U x⟩)
  let forwardNatural (p : conditions) : Prop :=
    ∀ U V (k : U ⟶ V),
      (ToInternal.carrier R L).obj.map k ≫ (↾(forwardApp p V)) =
        (↾(forwardApp p U)) ≫ (ToInternal.carrier (ringSheaf JC O) M).obj.map k
  let forwardCarrier (p : conditions) (q : forwardNatural p) :
      ToInternal.carrier R L ⟶ ToInternal.carrier (ringSheaf JC O) M :=
    ⟨{ app := fun U ↦ ↾(forwardApp p U), naturality := fun U V k ↦ q U V k }⟩
  let linear (p : conditions) (q : forwardNatural p) : Prop :=
    (∀ U (x y : L.val.obj U), forwardApp p U (x + y) =
      forwardApp p U x + forwardApp p U y) ∧
    (∀ U (r : R.obj.obj U) (x : L.val.obj U), forwardApp p U (r • x) =
      (((SheafOfModules.restrictScalars i.structureMap).obj M).val.obj U).isModule.smul
        r (forwardApp p U x)) ∧
    (∀ U (x y : M.val.obj U), underlyingApp (ringSheaf JC O) (reverseMap p) U (x + y) =
      underlyingApp (ringSheaf JC O) (reverseMap p) U x +
        underlyingApp (ringSheaf JC O) (reverseMap p) U y) ∧
    (∀ U (r : (ringSheaf JC O).obj.obj U) (x : M.val.obj U),
      underlyingApp (ringSheaf JC O) (reverseMap p) U (r • x) =
        r • underlyingApp (ringSheaf JC O) (reverseMap p) U x)
  let forward (p : conditions) (q : forwardNatural p) (r : linear p q) :
      idealModule i ⟶ M :=
    (extendRestrictHomEquiv i.structureMap L M).symm
      (homOfUnderlying R (forwardCarrier p q) r.1 r.2.1)
  let backward (p : conditions) (q : forwardNatural p) (r : linear p q) :
      M ⟶ idealModule i :=
    homOfUnderlying (ringSheaf JC O) (reverseMap p) r.2.2.1 r.2.2.2
  have laws : conditions ∧ (∀ p : conditions,
      forwardNatural p ∧ (∀ q : forwardNatural p,
        linear p q ∧ (∀ r : linear p q,
          backward p q r ≫ forward p q r = 𝟙 M ∧
            forward p q r ≫ backward p q r = 𝟙 (idealModule i)))) := by
    sorry
  let p := laws.1
  let q := (laws.2 p).1
  let r := ((laws.2 p).2 q).1
  exact ⟨backward p q r, forward p q r,
    (((laws.2 p).2 q).2 r).1, (((laws.2 p).2 q).2 r).2⟩


variable [HasSheafify JC AddCommGrpCat.{max uC vC}]
variable [(SheafOfModules.restrictScalars (ringSheafMap (normalizedProjection i))).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max uC vC}
  (ringSheaf JC (normalizedRing i))]
variable [HasFunctorialInjectives
  (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)]
variable [HasExt.{wExt} (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)]

/-- The existence obstruction of a thickening is the normalized same-site obstruction,
with the infinitesimal map transported through the canonical ideal identification. -/
def existenceObstruction
    (F K : ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)
    (c : moduleTensor (idealModule i) F ⟶ K) : Ext F K 2 :=
  FirstOrderThickening.ModuleExtension.existenceObstruction (normalizedProjection i) F K
    (hπ := normalizedProjection_isFirstOrderThickening i)
    (moduleTensorMap (normalizedIdealIso i).hom (𝟙 F) ≫ c)

section Horizontal

variable {E : Type uE} [Category.{vE} E] {JE : GrothendieckTopology E}
variable [JE.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JE.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JE.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [HasSheafify JE AddCommGrpCat.{max uC vC}]
variable [JE.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable {O'' : Sheaf JE CommRingCat.{max uC vC}}
variable {i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD O')}
variable {i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JE O'')}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]

/-- A morphism of thickenings over a fixed ringed topos induces the same-site
morphism of their normalized square-zero ring sheaves. -/
def normalizedHom
    (h : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JE O''))
    (alpha : TwoIso (i1.comp h) i2) :
    @FirstOrderThickening.Hom _ _ _ _ _ _
      (normalizedProjection i1) (normalizedProjection i2)
      (normalizedProjection_isFirstOrderThickening i1)
      (normalizedProjection_isFirstOrderThickening i2) := by
  let comparison := MorphismOfTopoiIn.ringInverseImageNatIso
    (inverseImageIsoOfPushforwardIso (i1.comp h) i2 alpha.homIso)
  let ringMap := (i2.toTopos.commRingInverseImageForgetRingIso).hom.app O'' ≫
    comparison.inv.app (ringSheaf JE O'') ≫
    (MorphismOfTopoiIn.ringInverseImageCompIso h.toTopos i1.toTopos).hom.app
      (ringSheaf JE O'') ≫
    i1.toTopos.ringInverseImage.map h.structureMap ≫
    (i1.toTopos.commRingInverseImageForgetRingIso).inv.app O'
  let hom := (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing
    (J := JC)).preimage ringMap
  have comm : hom ≫ normalizedProjection i1 = normalizedProjection i2 := by
    sorry
  exact @FirstOrderThickening.Hom.mk _ _ _ _ _ _
    (normalizedProjection i1) (normalizedProjection i2)
    (normalizedProjection_isFirstOrderThickening i1)
    (normalizedProjection_isFirstOrderThickening i2) hom comm

variable [(SheafOfModules.restrictScalars.{max uC vC} i1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} i2.structureMap).IsRightAdjoint]

/-- Normalized ideal transport agrees with the canonical geometric ideal map
under the two normalized ideal identifications. -/
theorem normalizedHom_idealMap
    (h : ToposHom (ofCommRingSheaf JD O') (ofCommRingSheaf JE O''))
    (alpha : TwoIso (i1.comp h) i2)
    [(SheafOfModules.restrictScalars.{max uC vC} h.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{max uC vC} (i1.comp h).structureMap).IsRightAdjoint] :
    @FirstOrderThickening.Hom.idealMap _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (normalizedProjection_isFirstOrderThickening i1)
      (normalizedProjection_isFirstOrderThickening i2) (normalizedHom h alpha) ≫
      (normalizedIdealIso i1).hom =
      (normalizedIdealIso i2).hom ≫ idealHom h alpha := by
  sorry

end Horizontal

end RingedSite.ToposHom.Thickening
