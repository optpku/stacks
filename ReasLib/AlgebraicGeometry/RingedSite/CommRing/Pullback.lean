module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.CommRingCat
public import ReasLib.Algebra.Category.CommRingCat.Colimits
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of commutative structure sheaves on ringed sites

This leaf owns the commutative-ring presentation of the structure map of a morphism between
ringed sites with independently sized site categories. It is independent of flatness and of
module-theoretic properties.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom

section Base

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒜 : Sheaf JC CommRingCat.{w}} {𝒜' : Sheaf JD CommRingCat.{w}}

/-- The base functor of a morphism between commutative ringed-site presentations is continuous.
The coefficient universe is independent of the sizes of the two site categories. -/
@[stacks 03D6 "continuous base functor"]
instance commRingBaseIsContinuous
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒜)
      (RingedSite.ofCommRingSheaf JD 𝒜')) :
    Functor.IsContinuous f.base JD JC :=
  RingedSite.Hom.base_isContinuous f

end Base

section CommRing

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪 : Sheaf JC CommRingCat.{w}}
variable {𝒪' : Sheaf JD CommRingCat.{w}}

/-- The inverse-image commutative structure sheaf `f⁻¹𝒪_Y` attached to a morphism of
commutative ringed-site presentations. -/
@[stacks 03D6 "inverse-image commutative structure sheaf"]
abbrev inverseImageStructureSheaf
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    Sheaf JC CommRingCat.{w} :=
  (f.base.sheafPullback CommRingCat.{w} JD JC).obj 𝒪'

/-- Textbook notation for the inverse-image commutative structure sheaf `f⁻¹𝒪_Y`. -/
scoped notation:max f:max "⁻¹𝒪" => inverseImageStructureSheaf f

/-- The pushforward-form structure-sheaf morphism after forgetting commutativity. -/
abbrev underlyingStructureSheafMap
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪')) :
    (sheafCompose JD
      (forget₂ CommRingCat.{w} RingCat.{w})).obj 𝒪' ⟶
      (sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((f.base.sheafPushforwardContinuous
          CommRingCat.{w} JD JC).obj 𝒪) :=
  f.structureSheafMap

/-- The pushforward-form structure-sheaf morphism in `CommRingCat`.  It is the unique lift of
`underlyingStructureSheafMap f` through the fully faithful forgetful functor from commutative
rings to rings. -/
@[stacks 03D6 "commutative structure-sheaf map"]
noncomputable abbrev commRingStructureSheafMap
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪')) :
    𝒪' ⟶
      (f.base.sheafPushforwardContinuous
        CommRingCat.{w} JD JC).obj 𝒪 :=
  Functor.preimage
    (sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w}))
    (underlyingStructureSheafMap f)

/-- The adjoint same-site form `inverseImageStructureSheafMap f : f⁻¹𝒪 ⟶ 𝒪` of the
structure-sheaf map of a commutative ringed-site presentation. -/
@[stacks 03D6 "inverse-image structure-sheaf map"]
abbrev inverseImageStructureSheafMap
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    f⁻¹𝒪 ⟶ 𝒪 :=
  ((f.base.sheafAdjunctionContinuous
    CommRingCat.{w} JD JC).homEquiv _ _).symm
    (Functor.preimage (sheafCompose JD
      (forget₂ CommRingCat.{w} RingCat.{w}))
      (underlyingStructureSheafMap f))

/-- Transposing `inverseImageStructureSheafMap f` through the sheaf pullback-pushforward
adjunction recovers the original pushforward-form structure-sheaf map. -/
theorem inverseImageStructureSheafMap_homEquiv
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    ((f.base.sheafAdjunctionContinuous
      CommRingCat.{w} JD JC).homEquiv _ _)
      (inverseImageStructureSheafMap f) =
      Functor.preimage (sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w}))
        (underlyingStructureSheafMap f) := sorry

end CommRing

end RingedSite.Hom


-- The three data-bearing declarations are inherited canonical sheaf constructions.
