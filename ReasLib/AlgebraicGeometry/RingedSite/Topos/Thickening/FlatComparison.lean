/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Strict
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Unit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Ideal comparison for strict flat morphisms of thickenings -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

namespace RingedSite.ToposHom.Thickening

variable {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
variable {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
variable [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify B.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify D.siteTopology AddCommGrpCat.{w}]
variable [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [D.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (sq : CommSquare A B C D)

section Ambient

variable [IsThickening sq.upper] [IsThickening sq.lower]
variable [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]

/-- For a strict square with flat ambient morphism, the pulled-back ambient kernel
ideal is canonically the source ambient kernel ideal. -/
def idealIsoOfStrictFlat (strict : IsStrict sq) (flat : IsFlat sq.right) :
    sq.right.modulePullback.obj (ker sq.lower) ≅ ker sq.upper := by
  let P := sq.right.modulePullback
  let g := kernelMap sq.lower
  let j := kernelIdeal_ι sq.upper
  let u := modulePullbackUnitIso sq.right
  have zeroPres : P.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ P
      sq.right.moduleAdjunction.isLeftAdjoint
  have finite : PreservesFiniteLimits P :=
    (@IsFlat.exactPullback _ _ _ _ sq.right inferInstance flat).property.1
  have preserve : PreservesLimit (parallelPair g 0) P :=
    @PreservesLimitsOfShape.preservesLimit _ _ _ _ _ _ P
      (finite.preservesFiniteLimits WalkingParallelPair) (parallelPair g 0)
  let comparison := @PreservesKernel.iso _ _ _ _ _ _ P zeroPres _ _ g
    inferInstance inferInstance preserve
  let condition : Prop := (j ≫ u.inv) ≫ P.map g = 0
  let reverse (p : condition) := kernel.lift (P.map g) (j ≫ u.inv) p ≫ comparison.inv
  have laws : condition ∧ (∀ p : condition,
      idealMap sq ≫ reverse p = 𝟙 _ ∧ reverse p ≫ idealMap sq = 𝟙 _) := by
    sorry
  exact ⟨idealMap sq, reverse laws.1, (laws.2 laws.1).1, (laws.2 laws.1).2⟩

/-- The forward ambient ideal comparison is the canonical kernel comparison. -/
theorem idealIsoOfStrictFlat_hom (strict : IsStrict sq) (flat : IsFlat sq.right) :
    (idealIsoOfStrictFlat sq strict flat).hom = idealMap sq := rfl

end Ambient

section Source

variable [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
variable [IsFirstOrderThickening sq.upper] [IsFirstOrderThickening sq.lower]
variable [(SheafOfModules.restrictScalars.{w} sq.left.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} sq.lower.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp sq.left sq.lower).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp sq.upper sq.right).structureMap).IsRightAdjoint]

/-- Strictness and ambient flatness identify the source ideal with the pulled-back
base ideal through the canonical composition and square-cell transports. -/
def sourceIdealIsoOfStrictFlat (strict : IsStrict sq) (flat : IsFlat sq.right) :
    sq.left.modulePullback.obj (idealModule sq.lower) ≅ idealModule sq.upper :=
  ((modulePullbackCompIso sq.left sq.lower).app (kernelIdeal sq.lower)).symm ≪≫
    ((modulePullbackIsoOfTwoIso sq.cell).app (kernelIdeal sq.lower)).symm ≪≫
      (modulePullbackCompIso sq.upper sq.right).app (kernelIdeal sq.lower) ≪≫
        sq.upper.modulePullback.mapIso (idealIsoOfStrictFlat sq strict flat)

/-- The forward source ideal isomorphism is exactly the canonical source ideal map. -/
theorem sourceIdealIsoOfStrictFlat_hom (strict : IsStrict sq) (flat : IsFlat sq.right) :
    (sourceIdealIsoOfStrictFlat sq strict flat).hom = sourceIdealMap sq := rfl

end Source

end RingedSite.ToposHom.Thickening
