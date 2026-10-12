/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Pushout
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.RepresentableBy.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.IsPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Explicit internal-hom comparisons for simplicial-set pushouts

This leaf owns the comparison, explicit inverse, and isomorphism for arbitrary representing
objects. Chosen internal-hom comparisons are specializations in `Pushout.Comparison`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.pushout

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasCopowers (pushout a b) C]
variable {T : SimplicialObject C}
variable {MU MV MW MP : SimplicialObject C}
variable (RU : (presheaf U T).RepresentableBy MU)
variable (RV : (presheaf V T).RepresentableBy MV)
variable (RW : (presheaf W T).RepresentableBy MW)
variable (RP : (presheaf (CategoryTheory.Limits.pushout a b) T).RepresentableBy MP)

namespace comparisonOf

/-- The two composites between arbitrary explicit representing objects agree over the source
of a simplicial-set span. -/
@[stacks 017N "compatibility for explicit internal-hom representations"]
theorem condition :
    precompOf (CategoryTheory.Limits.pushout.inl a b) RV RP ≫ precompOf a RU RV =
      precompOf (CategoryTheory.Limits.pushout.inr a b) RW RP ≫ precompOf b RU RW := sorry

end comparisonOf

variable [HasPullback (precompOf a RU RV) (precompOf b RU RW)]

/-- The canonical comparison from an arbitrary explicit representation of the internal-hom
presheaf out of a pushout to the pullback of arbitrary representations on its span. -/
@[stacks 017N "comparison for explicit internal-hom representations"]
def comparisonOf :
    MP ⟶ pullback (precompOf a RU RV) (precompOf b RU RW) :=
  pullback.lift
    (precompOf (CategoryTheory.Limits.pushout.inl a b) RV RP)
    (precompOf (CategoryTheory.Limits.pushout.inr a b) RW RP)
    (comparisonOf.condition a b RU RV RW RP)

namespace comparisonOf

/-- The first projection of `comparisonOf` is explicit precomposition by the left pushout
coprojection. -/
@[reassoc (attr := simp), stacks 017N "first projection of the explicit internal-hom comparison"]
theorem fst :
    pushout.comparisonOf a b RU RV RW RP ≫
        pullback.fst (precompOf a RU RV) (precompOf b RU RW) =
      precompOf (CategoryTheory.Limits.pushout.inl a b) RV RP := sorry

/-- The second projection of `comparisonOf` is explicit precomposition by the right pushout
coprojection. -/
@[reassoc (attr := simp), stacks 017N "second projection of the explicit internal-hom comparison"]
theorem snd :
    pushout.comparisonOf a b RU RV RW RP ≫
        pullback.snd (precompOf a RU RV) (precompOf b RU RW) =
      precompOf (CategoryTheory.Limits.pushout.inr a b) RW RP := sorry

namespace inv

/-- The maps represented by the two pullback projections form a cocone over the copowered
span, for arbitrary explicit internal-hom representations. -/
@[stacks 017N "compatibility for the explicit inverse internal-hom comparison"]
theorem condition :
    copower.indexHom (pullback (precompOf a RU RV) (precompOf b RU RW)) a ≫
        RV.homEquiv (pullback.fst (precompOf a RU RV) (precompOf b RU RW)) =
      copower.indexHom (pullback (precompOf a RU RV) (precompOf b RU RW)) b ≫
        RW.homEquiv (pullback.snd (precompOf a RU RV) (precompOf b RU RW)) := sorry

/-- The copower cocone represented by the projections from the pullback of arbitrary
explicit internal-hom representations. -/
@[stacks 017N "cocone defining the explicit inverse internal-hom comparison"]
def cocone : PushoutCocone
    (copower.indexHom (pullback (precompOf a RU RV) (precompOf b RU RW)) a)
    (copower.indexHom (pullback (precompOf a RU RV) (precompOf b RU RW)) b) :=
  PushoutCocone.mk
    (RV.homEquiv (pullback.fst (precompOf a RU RV) (precompOf b RU RW)))
    (RW.homEquiv (pullback.snd (precompOf a RU RV) (precompOf b RU RW)))
    (condition a b RU RV RW)

end inv

/-- The inverse of the explicit internal-hom pushout comparison, constructed directly from
the four representing equivalences and copower descent. -/
@[stacks 017N "inverse comparison for explicit internal-hom representations"]
def inv : pullback (precompOf a RU RV) (precompOf b RU RW) ⟶ MP :=
  RP.homEquiv.symm
    (copower.pushout.desc.hom a b (pullback (precompOf a RU RV) (precompOf b RU RW))
      (inv.cocone a b RU RV RW))

namespace inv

/-- Under the pushout representing equivalence, `comparisonOf.inv` is copower descent from
the cocone represented by the two pullback projections. -/
@[stacks 017N "representation formula for the explicit inverse internal-hom comparison"]
theorem homEquiv :
    RP.homEquiv (pushout.comparisonOf.inv a b RU RV RW RP) =
      copower.pushout.desc.hom a b (pullback (precompOf a RU RV) (precompOf b RU RW))
        (cocone a b RU RV RW) := sorry

end inv

/-- The explicit comparison followed by its directly constructed inverse is the identity. -/
@[stacks 017N "forward-inverse law for the explicit internal-hom comparison"]
theorem hom_inv_id :
    pushout.comparisonOf a b RU RV RW RP ≫
      pushout.comparisonOf.inv a b RU RV RW RP = 𝟙 _ := sorry

/-- The directly constructed inverse followed by the explicit comparison is the identity. -/
@[stacks 017N "inverse-forward law for the explicit internal-hom comparison"]
theorem inv_hom_id :
    pushout.comparisonOf.inv a b RU RV RW RP ≫
      pushout.comparisonOf a b RU RV RW RP = 𝟙 _ := sorry

/-- Arbitrary explicit representations identify internal hom out of a simplicial-set pushout
with the pullback of the two restriction maps. -/
@[stacks 017N "explicit internal hom out of a pushout as a pullback"]
def iso : MP ≅ pullback (precompOf a RU RV) (precompOf b RU RW) where
  hom := pushout.comparisonOf a b RU RV RW RP
  inv := pushout.comparisonOf.inv a b RU RV RW RP
  hom_inv_id := hom_inv_id a b RU RV RW RP
  inv_hom_id := inv_hom_id a b RU RV RW RP

/-- The comparison between arbitrary explicit representations sends a simplicial-set pushout
to the corresponding pullback. -/
@[stacks 017N, instance]
theorem isIso : IsIso (pushout.comparisonOf a b RU RV RW RP) := sorry

end comparisonOf

end CategoryTheory.SimplicialObject.internalHom.pushout
