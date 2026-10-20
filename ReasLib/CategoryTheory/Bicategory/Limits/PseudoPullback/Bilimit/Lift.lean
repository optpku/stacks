module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Computations
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal lifts between bilimit pseudopullback squares

This file specializes the shape-independent `PseudoCone.lift` API to readable walking-cospan
squares. It owns the chosen apex map, its whole comparison, projection components, the bundled
cone morphism, and the uniqueness isomorphism. Identity, composition, and apex equivalences are
kept in downstream leaves.
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

/-- A chosen universal map from a pseudopullback cone `S` to a bilimit cone `T`.

This is the readable walking-cospan specialization of `PseudoCone.lift`, so the generic and
shape-specific APIs share one quasi-inverse choice. -/
noncomputable abbrev lift (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    S.pt ⟶ T.pt :=
  PseudoCone.lift S.toPseudoCone T.toPseudoCone

/-- The universal comparison sends `lift S T` to the cone transformation represented by `S`.
This is the primary specification of the chosen universal map. -/
noncomputable abbrev lift.comparisonIso (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (T.toPseudoCone.comparison S.pt).obj (lift S T) ≅ S.toPseudoCone.π :=
  PseudoCone.lift.comparisonIso S.toPseudoCone T.toPseudoCone

/-- The canonical morphism of readable pseudopullback cones whose apex map is the universal
lift. This packages the chosen lift together with its universal comparison modification, so
downstream constructions do not rebuild `homMk` by hand. -/
@[stacks 003Q "universal morphism of pseudopullback cones"]
noncomputable def lift.hom (S T : PseudoPullbackCone f g) [T.IsBilimit] : S ⟶ T :=
  homMk (lift S T) (lift.comparisonIso S T).hom

/-- The apex map of the canonical universal cone morphism is the chosen universal lift. -/
@[simp]
theorem lift.hom.map (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    PseudoPullbackCone.map (lift.hom S T) = lift S T := sorry

/-- The comparison modification of the canonical universal cone morphism is the forward
universal comparison. -/
@[simp]
theorem lift.hom.fac (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    PseudoPullbackCone.fac (lift.hom S T) =
      (lift.comparisonIso S T).hom := sorry

/-- The chosen universal map followed by the left leg of the bilimit cone is canonically
isomorphic to the left leg of the source cone. -/
noncomputable abbrev lift.fstIso (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    lift S T ≫ T.fst ≅ S.fst :=
  Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The forward map of `lift.fstIso` is the left-vertex component of the universal comparison
modification. -/
@[simp]
theorem lift.fstIso.hom (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.fstIso S T).hom =
      (lift.comparisonIso S T).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The inverse map of `lift.fstIso` is the left-vertex component of the inverse universal
comparison modification. -/
@[simp]
theorem lift.fstIso.inv (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.fstIso S T).inv =
      (lift.comparisonIso S T).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The chosen universal map followed by the right leg of the bilimit cone is canonically
isomorphic to the right leg of the source cone. -/
noncomputable abbrev lift.sndIso (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    lift S T ≫ T.snd ≅ S.snd :=
  Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The forward map of `lift.sndIso` is the right-vertex component of the universal comparison
modification. -/
@[simp]
theorem lift.sndIso.hom (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.sndIso S T).hom =
      (lift.comparisonIso S T).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

/-- The inverse map of `lift.sndIso` is the right-vertex component of the inverse universal
comparison modification. -/
@[simp]
theorem lift.sndIso.inv (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.sndIso S T).inv =
      (lift.comparisonIso S T).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

/-- The chosen universal map followed by the central leg of the bilimit cone is canonically
isomorphic to the central leg of the source cone. -/
noncomputable abbrev lift.baseIso (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    lift S T ≫ (T.fst ≫ f) ≅ S.fst ≫ f :=
  Pseudofunctor.StrongTrans.isoApp (lift.comparisonIso S T)
    (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- The forward map of `lift.baseIso` is the central component of the universal comparison
modification. -/
@[simp]
theorem lift.baseIso.hom (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.baseIso S T).hom =
      (lift.comparisonIso S T).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) := sorry

/-- The inverse map of `lift.baseIso` is the central component of the inverse universal
comparison modification. -/
@[simp]
theorem lift.baseIso.inv (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    (lift.baseIso S T).inv =
      (lift.comparisonIso S T).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) := sorry

/-- The first-leg cell of the canonical universal cone morphism is the forward universal
first-projection comparison. -/
@[simp]
theorem lift.hom.fstFac (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    fstFac (lift.hom S T) = (lift.fstIso S T).hom := sorry

/-- The second-leg cell of the canonical universal cone morphism is the forward universal
second-projection comparison. -/
@[simp]
theorem lift.hom.sndFac (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    sndFac (lift.hom S T) = (lift.sndIso S T).hom := sorry

/-- The central cell of the canonical universal cone morphism is the forward universal
central-leg comparison. -/
@[simp]
theorem lift.hom.baseFac (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    baseFac (lift.hom S T) = (lift.baseIso S T).hom := sorry

/-- In a locally groupoidal bicategory, the first-leg isomorphism of the canonical universal cone
morphism is the chosen universal first-projection comparison. -/
@[simp]
theorem lift.hom.fstIso [IsLocallyGroupoid B]
    (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    PseudoPullbackCone.fstIso (lift.hom S T) = lift.fstIso S T := sorry

/-- In a locally groupoidal bicategory, the second-leg isomorphism of the canonical universal cone
morphism is the chosen universal second-projection comparison. -/
@[simp]
theorem lift.hom.sndIso [IsLocallyGroupoid B]
    (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    PseudoPullbackCone.sndIso (lift.hom S T) = lift.sndIso S T := sorry

/-- In a locally groupoidal bicategory, the central isomorphism of the canonical universal cone
morphism is the chosen universal central-leg comparison. -/
@[simp]
theorem lift.hom.baseIso [IsLocallyGroupoid B]
    (S T : PseudoPullbackCone f g) [T.IsBilimit] :
    PseudoPullbackCone.baseIso (lift.hom S T) = lift.baseIso S T := sorry

/-- Any other apex map whose comparison presents `S` is canonically isomorphic to `lift S T`.
This makes downstream arguments independent of the noncomputable preimage choice. -/
noncomputable abbrev lift.uniqueIso (S T : PseudoPullbackCone f g) [T.IsBilimit]
    (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅ S.toPseudoCone.π) :
    l ≅ lift S T :=
  PseudoCone.lift.uniqueIso S.toPseudoCone T.toPseudoCone l e

/-- Mapping the forward cell of `lift.uniqueIso` through the universal comparison recovers the
specified comparison followed by the inverse chosen lift comparison. -/
@[simp]
theorem lift.uniqueIso.map_hom (S T : PseudoPullbackCone f g) [T.IsBilimit]
    (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅ S.toPseudoCone.π) :
    (T.toPseudoCone.comparison S.pt).map (lift.uniqueIso S T l e).hom =
      (e ≪≫ (lift.comparisonIso S T).symm).hom := sorry

/-- Mapping the inverse cell of `lift.uniqueIso` through the universal comparison recovers the
inverse of the specified comparison composite. -/
@[simp]
theorem lift.uniqueIso.map_inv (S T : PseudoPullbackCone f g) [T.IsBilimit]
    (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅ S.toPseudoCone.π) :
    (T.toPseudoCone.comparison S.pt).map (lift.uniqueIso S T l e).inv =
      (e ≪≫ (lift.comparisonIso S T).symm).inv := sorry

/- Data audit (mathlib 4.32): the chosen lift, comparison, and uniqueness isomorphism are direct
walking-cospan specializations of the single shape-independent `PseudoCone` quasi-inverse owner.
Projection isomorphisms are components of the same whole comparison, so this file introduces no
second preimage, inverse, or comparison choice. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
