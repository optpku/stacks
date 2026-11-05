module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.CommRingCat
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutative ringed-site presentations

A continuous site functor together with a map from the inverse-image structure sheaf determines a
morphism of commutative ringed-site presentations.  Keeping this constructor explicit removes the
need for downstream APIs to carry a raw `F`, two sheaves, and an unrelated `fSharp` separately.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪C : Sheaf JC CommRingCat.{w}}
variable {𝒪D : Sheaf JD CommRingCat.{w}}

/-- Bundle a morphism of commutative ringed-site presentations from its inverse-image-form
structure-sheaf map. -/
@[stacks 03D6 "inverse-image presentation"]
noncomputable def ofInverseImageMap
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [(F.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (fSharp : (F.sheafPullback CommRingCat.{w} JD JC).obj 𝒪D ⟶ 𝒪C) :
    RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D) where
  base := F
  isMorphismOfSites := inferInstance
  structureSheafMap :=
    (sheafCompose JD (forget₂ CommRingCat RingCat)).map
      ((F.sheafAdjunctionContinuous CommRingCat.{w} JD JC).homEquiv _ _ fSharp)

/-- The canonical morphism from the inverse-image commutative ringed-site presentation to the
original presentation; its inverse-image-form structure map is the identity. -/
@[stacks 04KR "canonical inverse-image presentation"]
noncomputable def ofPullback
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [(F.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{w}) :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC
        ((F.sheafPullback CommRingCat.{w} JD JC).obj 𝒪D))
      (RingedSite.ofCommRingSheaf JD 𝒪D) :=
  ofInverseImageMap F (𝟙 ((F.sheafPullback CommRingCat.{w} JD JC).obj 𝒪D))

/-- The displayed base functor of `ofPullback` retains the continuity instance of the original
site functor. -/
instance ofPullback_base_isContinuous
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [(F.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{w}) :
    (ofPullback (JC := JC) (JD := JD) F 𝒪D).base.IsContinuous JD JC :=
  (inferInstance : F.IsContinuous JD JC)

/-- The right-adjoint structure on the displayed base functor of `ofPullback` is the canonical
one supplied for the original site functor. -/
instance ofPullback_pushforward_isRightAdjoint
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [h_adj : (F.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{w}) :
    ((ofPullback (JC := JC) (JD := JD) F 𝒪D).base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint :=
  h_adj



end RingedSite.Hom
