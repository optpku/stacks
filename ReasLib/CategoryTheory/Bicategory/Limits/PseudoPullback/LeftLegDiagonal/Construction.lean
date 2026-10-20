module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Diagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction

/-!
# Left-leg diagonal squares in a bicategory

This file constructs the generic bicategorical square underlying Stacks Project Lemma `04YR`.
It works with explicitly chosen pseudopullback cones and keeps the ordinary `Cat` model out of
the semantic owner.

For a square `P` over `f` and `g`, a bilimit self-pullback `Q` of `P.snd`, and a bilimit
self-pullback `R` of `f`, the construction consists of:

* the cospan transformation induced by `P.fst` and `P.iso`;
* its universal map `Q.pt ⟶ R.pt`;
* the relative diagonals into `Q` and `R`;
* the canonical comparison between the two composites, obtained by presenting both composites
  as the same cone and applying bilimit uniqueness.

All non-`Prop` presentation components are explicit pastings of associators, unitors, projection
comparisons, and the existing universal uniqueness isomorphism. Only their walking-cospan
naturality equations are deferred proof obligations.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

noncomputable section
/-- The cospan transformation induced by the first leg of a pseudopullback cone.

Both endpoint maps are `P.fst`, the base map is `g`, and both generating comparison
isomorphisms are the square comparison `P.iso`.
-/
def transform (P : PseudoPullbackCone f g) :
    CospanTransform P.snd P.snd f f :=
  CospanTransform.mk P.fst P.fst g P.iso P.iso

/-- The first leg of `P` induces a universal map from a chosen self-pseudopullback of `P.snd`
to a chosen bilimit self-pseudopullback of `f`.
-/
def map (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] : Q.pt ⟶ R.pt :=
  PseudoPullbackCone.mapCospan Q R (transform P)

/-- The relative diagonal of the second leg of `P`, valued in the chosen bilimit cone `Q`.
-/
def sourceDiagonal (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    P.pt ⟶ Q.pt :=
  PseudoPullbackCone.lift (PseudoPullbackCone.diagonal P.snd) Q

/-- The relative diagonal of `f`, valued in the chosen bilimit cone `R`.
-/
def targetDiagonal (R : PseudoPullbackCone f f) [R.IsBilimit] :
    x ⟶ R.pt :=
  PseudoPullbackCone.lift (PseudoPullbackCone.diagonal f) R

namespace sourceDiagonal

/-- The source relative diagonal followed by the first projection is canonically the
identity of `P.pt`. -/
def fstIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    LeftLegDiagonal.sourceDiagonal P Q ≫ Q.fst ≅ 𝟙 P.pt :=
  PseudoPullbackCone.lift.fstIso (PseudoPullbackCone.diagonal P.snd) Q

/-- The source relative diagonal followed by the second projection is canonically the
identity of `P.pt`. -/
def sndIso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    LeftLegDiagonal.sourceDiagonal P Q ≫ Q.snd ≅ 𝟙 P.pt :=
  PseudoPullbackCone.lift.sndIso (PseudoPullbackCone.diagonal P.snd) Q

end sourceDiagonal

namespace targetDiagonal

/-- The target relative diagonal followed by the first projection is canonically the
identity of `x`. -/
def fstIso (R : PseudoPullbackCone f f) [R.IsBilimit] :
    LeftLegDiagonal.targetDiagonal R ≫ R.fst ≅ 𝟙 x :=
  PseudoPullbackCone.lift.fstIso (PseudoPullbackCone.diagonal f) R

/-- The target relative diagonal followed by the second projection is canonically the
identity of `x`. -/
def sndIso (R : PseudoPullbackCone f f) [R.IsBilimit] :
    LeftLegDiagonal.targetDiagonal R ≫ R.snd ≅ 𝟙 x :=
  PseudoPullbackCone.lift.sndIso (PseudoPullbackCone.diagonal f) R

end targetDiagonal

/-- The cone on the self-cospan `f, f` obtained by using `P.fst` for both projections.

This is the common readable presentation of the two composites compared in the left-leg
diagonal square.
-/
def cone (P : PseudoPullbackCone f g) : PseudoPullbackCone f f where
  pt := P.pt
  fst := P.fst
  snd := P.fst
  iso := Iso.refl _


end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal
