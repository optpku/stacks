module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic bilimit API for pseudopullback squares

This file specializes the neutral conical-bilimit existence and bundle API to readable
pseudopullback squares. Universal lifts, their functoriality, and equivalences between chosen
apices live in downstream leaves.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B}

/-- Two `1`-morphisms with a common target admit a pseudopullback when their canonical
walking-cospan pseudodiagram admits a bilimit.

This is the bicategorical analogue of mathlib's `Limits.HasPullback f g`; it specializes the
neutral `HasBilimit` owner instead of introducing another universal-property class. -/
abbrev HasPseudoPullback (f : x ⟶ z) (g : y ⟶ z) : Prop :=
  HasBilimit (cospan f g)

/-- A bicategory has pseudopullbacks when it has all bilimits of walking-cospan shape.

As with mathlib's `Limits.HasPullbacks`, this is a shape specialization of the general
existence API. -/
abbrev HasPseudoPullbacks (B : Type u) [Bicategory.{w, v} B] : Prop :=
  HasBilimitsOfShape (LocallyDiscrete Limits.WalkingCospan) B

/-- An explicitly supplied readable bilimit square proves existence of a pseudopullback. -/
theorem HasPseudoPullback.mk {f : x ⟶ z} {g : y ⟶ z}
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    HasPseudoPullback f g := sorry
/- Proof strategy: bundle `S.toPseudoCone` with `BilimitCone.ofIsBilimit`, then apply
`HasBilimit.mk`. -/

/-- Pointwise existence of readable pseudopullbacks supplies all bilimits of walking-cospan
shape. This is the bicategorical counterpart of constructing `HasPullbacks` from pullbacks of
all pairs of arrows. -/
theorem HasPseudoPullbacks.mk
    (h : ∀ {x y z : B} (f : x ⟶ z) (g : y ⟶ z), HasPseudoPullback f g) :
    HasPseudoPullbacks B := sorry
/- Proof strategy: normalize an arbitrary locally discrete walking-cospan pseudofunctor to the
canonical cospan on its two generating maps, use `h`, and transport the bilimit across the
resulting diagram equivalence. -/

namespace PseudoPullbackCone

variable {f : x ⟶ z} {g : y ⟶ z}

/-- Bundle a readable pseudopullback cone using an explicitly supplied bilimit proof. -/
def toBilimitConeOfIsBilimit (S : PseudoPullbackCone f g) (hS : S.IsBilimit) :
    BilimitCone (cospan f g) where
  cone := S.toPseudoCone
  isBilimit := hS

/- Proof strategy: use the supplied proof as the `BilimitCone` field without selecting any
additional cone data. -/

/-- Bundle a readable bilimit pseudopullback cone as the neutral `BilimitCone` on its
walking-cospan diagram. -/
def toBilimitCone (S : PseudoPullbackCone f g) [S.IsBilimit] :
    BilimitCone (cospan f g) :=
  toBilimitConeOfIsBilimit S inferInstance

/-- The pseudocone underlying the bundled bilimit cone is the canonical normalization of the
readable square. -/
@[simp]
theorem toBilimitCone.cone (S : PseudoPullbackCone f g) [S.IsBilimit] :
    S.toBilimitCone.cone = S.toPseudoCone := sorry
/- Proof strategy: unfold `toBilimitCone` and apply `BilimitCone.ofIsBilimit_cone`. -/

end PseudoPullbackCone

namespace BilimitCone

variable {f : x ⟶ z} {g : y ⟶ z}

/-- The readable pseudopullback-cone presentation of a bilimit cone on a walking cospan.

Only the presentation changes: the underlying readable square is obtained by the canonical
`PseudoPullbackCone.ofPseudoCone` normalization. -/
def toPseudoPullbackCone (L : BilimitCone (cospan f g)) :
    PseudoPullbackCone f g :=
  PseudoPullbackCone.ofPseudoCone L.cone

/-- The readable presentation of a bundled walking-cospan bilimit cone carries the canonical
bilimit instance inherited from the stored generic cone. -/
theorem toPseudoPullbackCone.isBilimit (L : BilimitCone (cospan f g)) :
    L.toPseudoPullbackCone.IsBilimit := sorry

/-- The readable presentation of a bilimit cone has the same apex as its generic cone. -/
@[simp]
theorem toPseudoPullbackCone.pt (L : BilimitCone (cospan f g)) :
    L.toPseudoPullbackCone.pt = L.cone.pt := sorry
/- Proof strategy: apply `PseudoPullbackCone.ofPseudoCone.pt`. -/

/-- The first projection of the readable presentation is the left-vertex cone component. -/
@[simp]
theorem toPseudoPullbackCone.fst (L : BilimitCone (cospan f g)) :
    L.toPseudoPullbackCone.fst =
      L.cone.π.app (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry
/- Proof strategy: apply `PseudoPullbackCone.ofPseudoCone.fst`. -/

/-- The second projection of the readable presentation is the right-vertex cone component. -/
@[simp]
theorem toPseudoPullbackCone.snd (L : BilimitCone (cospan f g)) :
    L.toPseudoPullbackCone.snd =
      L.cone.π.app (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry
/- Proof strategy: apply `PseudoPullbackCone.ofPseudoCone.snd`. -/

/-- The comparison of the readable presentation is assembled from the two generating
naturality isomorphisms of the generic cone. -/
@[simp]
theorem toPseudoPullbackCone.iso (L : BilimitCone (cospan f g)) :
    L.toPseudoPullbackCone.iso =
      (L.cone.π.naturality
          (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm ≪≫
        L.cone.π.naturality
          (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr) := sorry
/- Proof strategy: apply `PseudoPullbackCone.ofPseudoCone.iso`. -/

end BilimitCone

namespace PseudoPullbackCone

variable {f : x ⟶ z} {g : y ⟶ z}

/-- Passing a readable bilimit pseudopullback cone to the generic bundle and back recovers the
original readable cone. -/
@[simp]
theorem toBilimitCone.toPseudoPullbackCone
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    S.toBilimitCone.toPseudoPullbackCone = S := sorry
/- Proof strategy: unfold both bundle bridges and apply `ofPseudoCone.toPseudoCone`. -/

end PseudoPullbackCone

namespace BilimitCone

variable {f : x ⟶ z} {g : y ⟶ z}

/-- Passing a walking-cospan bilimit cone to its readable pseudopullback presentation and back
recovers the original bundled bilimit cone. -/
@[simp]
theorem toPseudoPullbackCone.toBilimitCone (L : BilimitCone (cospan f g)) :
    PseudoPullbackCone.toBilimitConeOfIsBilimit L.toPseudoPullbackCone
      (toPseudoPullbackCone.isBilimit L) = L := sorry

end BilimitCone

/- Data audit (mathlib 4.32): both bundle bridges preserve the explicitly supplied cone data.
Any `sorryAx` dependency is confined to bilimit evidence and inherited pseudocone coherence;
neither direction chooses an apex, projection, comparison, or universal map. -/

end Bicategory

end CategoryTheory
