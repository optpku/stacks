module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison

/-! # Horizontal transport of ideals of first-order thickenings -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ w

namespace RingedSite.ToposHom.Thickening

variable {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
variable {C : RingedSite.{u₂, v₂, w}}
variable [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify B.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify C.siteTopology AddCommGrpCat.{w}]
variable [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [C.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {i1 : ToposHom A B} {i2 : ToposHom A C}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [(SheafOfModules.restrictScalars.{w} i1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} i2.structureMap).IsRightAdjoint]

/-- A morphism between first-order thickenings over a fixed ringed topos induces a
map from the second source ideal to the first source ideal. -/
def idealHom (h : ToposHom B C) (alpha : TwoIso (i1.comp h) i2)
    [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (i1.comp h).structureMap).IsRightAdjoint] :
    idealModule i2 ⟶ idealModule i1 := by
  let toUnit := h.modulePullback.map (kernelIdeal_ι i2) ≫ modulePullbackObjUnitToUnit h
  have condition : toUnit ≫ kernelMap i1 = 0 := by
    sorry
  let ambient := kernel.lift (kernelMap i1) toUnit condition
  exact (modulePullbackIsoOfTwoIso alpha).inv.app (ker i2) ≫
    (modulePullbackCompIso i1 h).hom.app (ker i2) ≫ i1.modulePullback.map ambient

end RingedSite.ToposHom.Thickening
