/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift.Functoriality

/-!
# Equivalence of bilimit pseudopullback apices

This file packages the two universal lifts between readable bilimit squares as a bicategorical
equivalence. It exposes the whole walking-cospan comparisons, both projection isomorphisms in
both directions, and their component computations.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The identity and composition comparisons for readable universal lifts give a candidate
unit for the canonical equivalence between two bilimit apices. -/
noncomputable abbrev apexEquivalence.unitIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    𝟙 S.pt ≅ lift S T ≫ lift T S :=
  PseudoCone.apexEquivalence.unitIso S.toPseudoCone T.toPseudoCone

/-- The composition and identity comparisons for readable universal lifts give a candidate
counit for the canonical equivalence between two bilimit apices. -/
noncomputable abbrev apexEquivalence.counitIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    lift T S ≫ lift S T ≅ 𝟙 T.pt :=
  PseudoCone.apexEquivalence.counitIso S.toPseudoCone T.toPseudoCone

/-- Any two readable bilimit pseudopullback cones on the same cospan have canonically equivalent
apices. Its forward and inverse maps are the universal lifts in the two directions. -/
@[stacks 003Q "equivalence between bilimit pseudopullback apices"]
noncomputable abbrev apexEquivalence (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    S.pt ≌ T.pt :=
  PseudoCone.apexEquivalence S.toPseudoCone T.toPseudoCone

/-- The forward map of the canonical equivalence is the universal lift from the first cone to
the second. -/
@[simp]
theorem apexEquivalence.hom (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).hom = lift S T := sorry

/-- The inverse map of the canonical equivalence is the universal lift in the reverse
direction. -/
@[simp]
theorem apexEquivalence.inv (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).inv = lift T S := sorry

/-- The unit of the canonical apex equivalence is the readable universal-lift unit. -/
@[simp]
theorem apexEquivalence.unit (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).unit = apexEquivalence.unitIso S T := sorry

/-- The counit of the canonical apex equivalence is the adjointified readable lift counit. -/
@[simp]
theorem apexEquivalence.counit (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).counit =
      Bicategory.adjointifyCounit
        (apexEquivalence.unitIso S T) (apexEquivalence.counitIso S T) := sorry

/-- The whole walking-cospan comparison carried by the forward map of the canonical apex
equivalence. -/
noncomputable abbrev apexEquivalence.homComparisonIso
    (S T : PseudoPullbackCone f g) [S.IsBilimit] [T.IsBilimit] :
    (T.toPseudoCone.comparison S.pt).obj (apexEquivalence S T).hom ≅
      S.toPseudoCone.π :=
  PseudoCone.apexEquivalence.homComparisonIso S.toPseudoCone T.toPseudoCone

/-- The whole walking-cospan comparison carried by the inverse map of the canonical apex
equivalence. -/
noncomputable abbrev apexEquivalence.invComparisonIso
    (S T : PseudoPullbackCone f g) [S.IsBilimit] [T.IsBilimit] :
    (S.toPseudoCone.comparison T.pt).obj (apexEquivalence S T).inv ≅
      T.toPseudoCone.π :=
  PseudoCone.apexEquivalence.invComparisonIso S.toPseudoCone T.toPseudoCone

/-- The forward map of the canonical apex equivalence commutes with the first projection. -/
noncomputable abbrev apexEquivalence.homFstIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).hom ≫ T.fst ≅ S.fst :=
  Pseudofunctor.StrongTrans.isoApp (apexEquivalence.homComparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The forward map of the canonical apex equivalence commutes with the second projection. -/
noncomputable abbrev apexEquivalence.homSndIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).hom ≫ T.snd ≅ S.snd :=
  Pseudofunctor.StrongTrans.isoApp (apexEquivalence.homComparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The inverse map of the canonical apex equivalence commutes with the first projection. -/
noncomputable abbrev apexEquivalence.invFstIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).inv ≫ S.fst ≅ T.fst :=
  Pseudofunctor.StrongTrans.isoApp (apexEquivalence.invComparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The inverse map of the canonical apex equivalence commutes with the second projection. -/
noncomputable abbrev apexEquivalence.invSndIso (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence S T).inv ≫ S.snd ≅ T.snd :=
  Pseudofunctor.StrongTrans.isoApp (apexEquivalence.invComparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The forward cell of `apexEquivalence.homFstIso` is the universal first-projection
comparison. -/
@[simp]
theorem apexEquivalence.homFstIso.hom (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homFstIso S T).hom = (lift.fstIso S T).hom := sorry

/-- The inverse cell of `apexEquivalence.homFstIso` is the inverse universal first-projection
comparison. -/
@[simp]
theorem apexEquivalence.homFstIso.inv (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homFstIso S T).inv = (lift.fstIso S T).inv := sorry

/-- The forward cell of `apexEquivalence.homSndIso` is the universal second-projection
comparison. -/
@[simp]
theorem apexEquivalence.homSndIso.hom (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homSndIso S T).hom = (lift.sndIso S T).hom := sorry

/-- The inverse cell of `apexEquivalence.homSndIso` is the inverse universal second-projection
comparison. -/
@[simp]
theorem apexEquivalence.homSndIso.inv (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.homSndIso S T).inv = (lift.sndIso S T).inv := sorry

/-- The forward inverse-direction first-projection cell is the reverse universal
comparison. -/
@[simp]
theorem apexEquivalence.invFstIso.hom (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invFstIso S T).hom = (lift.fstIso T S).hom := sorry

/-- The inverse inverse-direction first-projection cell is the inverse reverse universal
comparison. -/
@[simp]
theorem apexEquivalence.invFstIso.inv (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invFstIso S T).inv = (lift.fstIso T S).inv := sorry

/-- The forward inverse-direction second-projection cell is the reverse universal
comparison. -/
@[simp]
theorem apexEquivalence.invSndIso.hom (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invSndIso S T).hom = (lift.sndIso T S).hom := sorry

/-- The inverse inverse-direction second-projection cell is the inverse reverse universal
comparison. -/
@[simp]
theorem apexEquivalence.invSndIso.inv (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit] :
    (apexEquivalence.invSndIso S T).inv = (lift.sndIso T S).inv := sorry

/-- Every equivalence-closed object property has the same truth value on the apices of any two
readable bilimit pseudopullback cones over a fixed cospan. -/
theorem apexEquivalence.objectProperty_iff (S T : PseudoPullbackCone f g)
    [S.IsBilimit] [T.IsBilimit]
    (P : ObjectProperty B) [P.IsClosedUnderEquivalences] :
    P S.pt ↔ P T.pt := sorry

/- Data audit (mathlib 4.32): `apexEquivalence` is the walking-cospan specialization of the
shape-independent `PseudoCone.apexEquivalence`. Its maps are the existing lifts and all four
projection isomorphisms are components of the two existing whole comparisons. No additional
inverse, counit adjustment, object preimage, or comparison cell is chosen here. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
