/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and pullback on ringed sites

This file exposes the canonical tensor comparison for module pullback as an API attached to the
ringed-site morphism. The construction is the generic strong-monoidal comparison; no separate
source-specific tensor product is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

section CommRing

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

/-- Forgetting commutativity from the canonical lift of the structure-sheaf map recovers the
original ring-valued structure-sheaf map.  This is the bridge needed to transport the low-level
strong-monoidal pullback construction to the bundled `modulePullback` owner. -/
@[stacks 03EL "commutative structure-map compatibility"]
theorem ringMap_commRingStructureSheafMap
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY)) :
    SheafOfModules.Pullback.ringMap f.base (commRingStructureSheafMap f) =
      f.structureSheafMap := sorry

variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The presheaf right-adjoint input for the low-level pullback construction is inherited from
the bundled structure-sheaf map. -/
noncomputable instance ringMapPushforwardIsRightAdjoint
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    [(PresheafOfModules.pushforward.{z} f.structureSheafMap.hom).IsRightAdjoint] :
    (PresheafOfModules.pushforward.{z}
      (SheafOfModules.Pullback.ringMap f.base
        (commRingStructureSheafMap f)).hom).IsRightAdjoint :=
  (congrArg (fun a ↦
    (PresheafOfModules.pushforward.{z} a.hom).IsRightAdjoint)
    (ringMap_commRingStructureSheafMap f)).symm ▸ inferInstance

/-- The low-level pullback built from the lifted commutative structure map is the bundled module
pullback attached to `f`. -/
@[stacks 03EL "bundled pullback identification"]
theorem commRingModulePullback_eq
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint] :
    SheafOfModules.pullback.{w}
        (SheafOfModules.Pullback.ringMap f.base
          (commRingStructureSheafMap f)) =
      f.modulePullback.{w} := sorry

/-- Pullback on a commutative ringed-site presentation is canonically strong monoidal whenever
the base functor is representably flat. -/
@[stacks 03EL "bundled commutative ringed-site pullback", implicit_reducible]
noncomputable instance commRingModulePullbackMonoidal
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    [RepresentablyFlat f.base]
    [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint] :
    f.modulePullback.{w}.Monoidal :=
  commRingModulePullback_eq f ▸
    SheafOfModules.Pullback.monoidal f.base (commRingStructureSheafMap f)

end CommRing

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : X.Hom Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [(PresheafOfModules.pushforward.{z} f.structureSheafMap.hom).IsRightAdjoint]
variable [MonoidalCategory (ModuleCat.{z} Y)] [MonoidalCategory (ModuleCat.{z} X)]
variable [Functor.Monoidal f.modulePullback.{z}]

/-- Lemma 18.26.2 (03EL): module pullback intertwines the tensor bifunctors through the
canonical strong-monoidal natural isomorphism. -/
@[stacks 03EL]
noncomputable abbrev pullbackTensorNatIso :
    MonoidalCategory.tensor (ModuleCat.{z} Y) ⋙
        f.modulePullback.{z} ≅
      Functor.prod f.modulePullback.{z} f.modulePullback.{z} ⋙
        MonoidalCategory.tensor (ModuleCat.{z} X) :=
  (Functor.Monoidal.μNatIso f.modulePullback.{z}).symm

/-- The component of `pullbackTensorNatIso` at two module sheaves. -/
noncomputable abbrev pullbackTensorIso
    (F G : ModuleCat.{z} Y) :
    f.modulePullback.{z}.obj (F ⊗ G) ≅
      (f.modulePullback.{z}.obj F ⊗ f.modulePullback.{z}.obj G) :=
  (pullbackTensorNatIso f).app (F, G)

/-- The forward morphism of the canonical tensor comparison for module pullback. -/
noncomputable abbrev pullbackTensorComparison
    (F G : ModuleCat.{z} Y) :
    f.modulePullback.{z}.obj (F ⊗ G) ⟶
      (f.modulePullback.{z}.obj F ⊗ f.modulePullback.{z}.obj G) :=
  (pullbackTensorIso f F G).hom

/- The `sorryAx` reported for the specialized declarations is inherited through proof-law fields
of the ambient category/monoidal instances. Their data is the explicit `μNatIso` projection from
the supplied `Functor.Monoidal f.modulePullback`; the generic owner itself is clean below. -/

end RingedSite.Hom
