/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Evaluation

variable {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)

/-- The inverse image of the open source of a target crystalline object. -/
abbrev openSource (f : B.source ⟶ B'.source) (A' : B'.ringedSite) : Scheme.{u} :=
  pullback f A'.obj.1.source.hom

/-- The inverse-image open carries the divided powers on its zero ideal. -/
def zeroScheme (f : B.source ⟶ B'.source) (A' : B'.ringedSite) : DividedPowerScheme.{u} where
  scheme := openSource B B' f A'
  ideal := ⊥
  quasiCoherent := sorry
  dividedPowers := fun V ↦
    (congrFun Scheme.IdealSheafData.ideal_bot V).symm ▸
      dividedPowersBot Γ(openSource B B' f A', V)
  compatible := sorry

/-- The inverse-image open maps to the divided-power base through its closed fibre. -/
def sourceToBase (f : B.source ⟶ B'.source) (A' : B'.ringedSite) :
    DividedPowerScheme.Hom (zeroScheme B B' f A') B.dividedPowerScheme where
  base := pullback.fst f A'.obj.1.source.hom ≫ B.sourceToClosed ≫ B.ideal.subschemeι
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The inverse-image open maps to the actual target crystalline thickening. -/
def sourceToTarget (f : B.source ⟶ B'.source) (A' : B'.ringedSite) :
    DividedPowerScheme.Hom (zeroScheme B B' f A') A'.obj.1.dividedPowerScheme where
  base := pullback.snd f A'.obj.1.source.hom ≫ A'.obj.1.inclusion
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The two maps from the inverse-image open commute over the target divided-power base. -/
theorem sourceSquare
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    (A' : B'.ringedSite) :
    DividedPowerScheme.Hom.comp (sourceToTarget B B' f A') (targetToBase B' A') =
      DividedPowerScheme.Hom.comp (sourceToBase B B' f A') g := sorry

variable (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
  (f : B.source ⟶ B'.source)
  (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
  (A' : B'.ringedSite) (T : DividedPowerScheme.{u})
  (iDP : DividedPowerScheme.Hom T A'.obj.1.dividedPowerScheme)
  (πT : DividedPowerScheme.Hom T B.dividedPowerScheme)
  (hcart : DividedPowerScheme.IsPullback iDP πT (targetToBase B' A') g)

/-- The universal divided-power lift maps the inverse-image open to the pullback thickening. -/
def sourceToPullback : DividedPowerScheme.Hom (zeroScheme B B' f A') T :=
  hcart.lift (sourceToTarget B B' f A') (sourceToBase B B' f A')
    (sourceSquare B B' g f hf A')

/-- The inverse-image open maps to the canonical closed fibre of the divided-power pullback. -/
def sourceToZeroFiber : openSource B B' f A' ⟶ T.ideal.subscheme :=
  inv (Scheme.IdealSheafData.subschemeι (⊥ : (openSource B B' f A').IdealSheafData)) ≫
    (sourceToPullback B B' g f hf A' T iDP πT hcart).zeroFiberMap

/-- Projection of the induced closed-fibre map recovers the original source geometry. -/
theorem sourceToZeroFiber_comm :
    sourceToZeroFiber B B' g f hf A' T iDP πT hcart ≫ πT.zeroFiberMap =
      pullback.fst f A'.obj.1.source.hom ≫ B.sourceToClosed := sorry

/-- The prime is locally nilpotent on the inverse-image open of a crystalline source. -/
theorem openSource_nilpotent (f : B.source ⟶ B'.source) (A' : B'.ringedSite) :
    ∀ V : (openSource B B' f A').affineOpens,
      IsNilpotent (p : Γ(openSource B B' f A', V)) := sorry

/-- The inverse-image open over the divided-power pullback is a prime-local crystalline base. -/
def pullbackBase : Base.{u} p :=
  Base.of p T.scheme T.ideal T.quasiCoherent T.dividedPowers T.compatible
    (πT.base ≫ B.toSpec) (openSource B B' f A')
    (sourceToZeroFiber B B' g f hf A' T iDP πT hcart) (openSource_nilpotent B B' f A')

/-- The closed-fibre square for geometric restriction commutes. -/
theorem restrictionSquare :
    pullback.fst f A'.obj.1.source.hom ≫ B.sourceToClosed =
      (pullbackBase B B' g f hf A' T iDP πT hcart).sourceToClosed ≫ πT.zeroFiberMap := sorry

/-- Geometric restriction from the crystalline site of the inverse-image open over
the divided-power pullback to the original crystalline site. -/
def restriction :
    RingedSite.ToposHom (pullbackBase B B' g f hf A' T iDP πT hcart).ringedSite B.ringedSite :=
  Ringed.morphism (pullbackBase B B' g f hf A' T iDP πT hcart) B πT rfl
    (pullback.fst f A'.obj.1.source.hom) (restrictionSquare B B' g f hf A' T iDP πT hcart)

/-- The slice over a crystalline object records each actual thickening map to its thickening. -/
def sliceThickening (B' : Base.{u} p) (A' : B'.ringedSite) :
    (B'.ringedSite.localization A').carrier ⥤ Over A'.obj.1.thickening where
  obj A := Over.mk A.hom.hom.thickening
  map k := Over.homMk k.left.hom.thickening sorry
  map_id := sorry
  map_comp := sorry

/-- Open covers of a target thickening lift to covers in its crystalline slice. -/
theorem sliceThickening_isCocontinuous (B' : Base.{u} p) (A' : B'.ringedSite) :
    (sliceThickening B' A').IsCocontinuous (B'.ringedSite.localization A').siteTopology
      (StandardTopology.zariski.overTopology A'.obj.1.thickening) := sorry

/-- Thickening evaluation uses the identity on functions of every test thickening. -/
def evaluationStructureMap (B' : Base.{u} p) (A' : B'.ringedSite) :
    (sliceThickening B' A').op ⋙
        (Scheme.AssociatedModule.bigCommRingedSite .zariski A'.obj.1.thickening).structureSheaf.obj ⟶
      (B'.ringedSite.localization A').structureSheaf.obj where
  app A := 𝟙 _
  naturality := sorry

/-- Evaluation at a crystalline thickening is induced by actual slice-thickening maps
followed by the big-to-small Zariski projection. -/
def evaluation (B' : Base.{u} p) (A' : B'.ringedSite) :
    RingedSite.ToposHom (B'.ringedSite.localization A')
      (Scheme.AssociatedModule.smallCommRingedSite .zariski A'.obj.1.thickening) :=
  RingedSite.ToposHom.comp
    (X := B'.ringedSite.localization A')
    (Y := Scheme.AssociatedModule.bigCommRingedSite .zariski A'.obj.1.thickening)
    (Z := Scheme.AssociatedModule.smallCommRingedSite .zariski A'.obj.1.thickening)
    (@RingedSite.Cocontinuous.toRingedTopos (B'.ringedSite.localization A')
      (Scheme.AssociatedModule.bigCommRingedSite .zariski A'.obj.1.thickening)
      (sliceThickening B' A') (sliceThickening_isCocontinuous B' A')
      inferInstance inferInstance inferInstance inferInstance (evaluationStructureMap B' A'))
    (Ringed.baseSmallProjection A'.obj.1.thickening)

/-- The evaluation structure map fixes every function on a test thickening. -/
theorem evaluationStructureMap_app (B' : Base.{u} p) (A' : B'.ringedSite)
    (A : (B'.ringedSite.localization A').carrierᵒᵖ) :
    (evaluationStructureMap B' A').app A = 𝟙 _ := sorry

/-- Evaluation at a crystalline thickening is left exact on module sheaves. -/
theorem evaluation_preservesFiniteLimits (B' : Base.{u} p) (A' : B'.ringedSite) :
    PreservesFiniteLimits (evaluation B' A').modulePushforward := sorry

/-- Evaluation at a crystalline thickening is right exact on module sheaves. -/
theorem evaluation_preservesFiniteColimits (B' : Base.{u} p) (A' : B'.ringedSite) :
    PreservesFiniteColimits (evaluation B' A').modulePushforward := sorry

end AlgebraicGeometry.Scheme.Crystalline.Evaluation
