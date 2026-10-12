/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Presentation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Computations.Construction

/-!
# Computations for left-leg diagonal squares

This file exposes the construction at the levels used by downstream calculations: cospan
components, relative-diagonal projections, the two complete cone presentations, the resulting
uniqueness cells, and the fields of the final readable square.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

noncomputable section


/-!
# Presentation computations for left-leg diagonal squares

Vertex components and comparison formulas for the presentation layer.
-/

/-- The forward first-projection cell of the induced map is the universal projection cell
followed by the constructor readout for the left endpoint. -/
@[simp]
theorem map.fstIso.hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.fstIso P Q R).hom =
      (PseudoPullbackCone.mapCospan.fstIso Q R (transform P)).hom ≫
        (whiskerLeftIso Q.fst
          (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))).hom := sorry

/-- The inverse first-projection cell of the induced map has the reverse canonical pasting. -/
@[simp]
theorem map.fstIso.inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.fstIso P Q R).inv =
      (whiskerLeftIso Q.fst
        (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))).inv ≫
        (PseudoPullbackCone.mapCospan.fstIso Q R (transform P)).inv := sorry

/-- The forward second-projection cell of the induced map is the universal projection cell
followed by the constructor readout for the right endpoint. -/
@[simp]
theorem map.sndIso.hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.sndIso P Q R).hom =
      (PseudoPullbackCone.mapCospan.sndIso Q R (transform P)).hom ≫
        (whiskerLeftIso Q.snd
          (eqToIso (CospanTransform.mk_right P.fst P.fst g P.iso P.iso))).hom := sorry

/-- The inverse second-projection cell of the induced map has the reverse canonical pasting. -/
@[simp]
theorem map.sndIso.inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.sndIso P Q R).inv =
      (whiskerLeftIso Q.snd
        (eqToIso (CospanTransform.mk_right P.fst P.fst g P.iso P.iso))).inv ≫
        (PseudoPullbackCone.mapCospan.sndIso Q R (transform P)).inv := sorry


/-- At the left vertex, the complete source presentation is `source.fstIso`. -/
@[simp]
theorem presentation.left.iso.hom_app_left (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (source.fstIso P Q R).hom := sorry

/-- At the right vertex, the complete source presentation is `source.sndIso`. -/
@[simp]
theorem presentation.left.iso.hom_app_right (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (source.sndIso P Q R).hom := sorry

/-- At the left vertex, the complete target presentation is `target.fstIso`. -/
@[simp]
theorem presentation.right.iso.hom_app_left (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (target.fstIso P R).hom := sorry

/-- At the right vertex, the complete target presentation is `target.sndIso`. -/
@[simp]
theorem presentation.right.iso.hom_app_right (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (target.sndIso P R).hom := sorry

/-- Under the represented comparison, the forward source uniqueness cell is its explicit
presentation followed by the inverse chosen lift comparison. -/
@[simp]
theorem comparison.left.map_hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).map (comparison.left P Q R).hom =
      (presentation.left.iso P Q R ≪≫
        (PseudoPullbackCone.lift.comparisonIso (cone P) R).symm).hom := sorry

/-- Under the represented comparison, the forward target uniqueness cell is its explicit
presentation followed by the inverse chosen lift comparison. -/
@[simp]
theorem comparison.right.map_hom (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).map (comparison.right P R).hom =
      (presentation.right.iso P R ≪≫
        (PseudoPullbackCone.lift.comparisonIso (cone P) R).symm).hom := sorry

/-- The forward left-leg diagonal cell is the forward source uniqueness cell followed by the
inverse target uniqueness cell. -/
@[simp]
theorem iso.hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).hom =
      (comparison.left P Q R).hom ≫ (comparison.right P R).inv := sorry

/-- The inverse left-leg diagonal cell is the forward target uniqueness cell followed by the
inverse source uniqueness cell. -/
@[simp]
theorem iso.inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).inv =
      (comparison.right P R).hom ≫ (comparison.left P Q R).inv := sorry

/-- The apex of the left-leg diagonal square is `P.pt`. -/
@[simp]
theorem square.pt (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (square P Q R).pt = P.pt := sorry

/-- The first leg of the left-leg diagonal square is the source relative diagonal. -/
@[simp]
theorem square.fst (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (square P Q R).fst = sourceDiagonal P Q := sorry

/-- The second leg of the left-leg diagonal square is `P.fst`. -/
@[simp]
theorem square.snd (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (square P Q R).snd = P.fst := sorry

/-- The comparison of the left-leg diagonal square is the canonical left-leg comparison. -/
@[simp]
theorem square.iso (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (square P Q R).iso = iso P Q R := sorry

/-- The inverse left-vertex component of the source presentation is the inverse source projection cell. -/
@[simp]
theorem presentation.left.iso.inv_app_left (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (source.fstIso P Q R).inv := sorry

/-- The inverse right-vertex component of the source presentation is the inverse source projection cell. -/
@[simp]
theorem presentation.left.iso.inv_app_right (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (source.sndIso P Q R).inv := sorry

/-- The inverse left-vertex component of the target presentation is the inverse target projection cell. -/
@[simp]
theorem presentation.right.iso.inv_app_left (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (target.fstIso P R).inv := sorry

/-- The inverse right-vertex component of the target presentation is the inverse target projection cell. -/
@[simp]
theorem presentation.right.iso.inv_app_right (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (target.sndIso P R).inv := sorry

/-- Under the represented comparison, the inverse source uniqueness cell is the inverse explicit presentation. -/
@[simp]
theorem comparison.left.map_inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).map (comparison.left P Q R).inv =
      (presentation.left.iso P Q R ≪≫
        (PseudoPullbackCone.lift.comparisonIso (cone P) R).symm).inv := sorry

/-- Under the represented comparison, the inverse target uniqueness cell is the inverse explicit presentation. -/
@[simp]
theorem comparison.right.map_inv (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (R.toPseudoCone.comparison P.pt).map (comparison.right P R).inv =
      (presentation.right.iso P R ≪≫
        (PseudoPullbackCone.lift.comparisonIso (cone P) R).symm).inv := sorry


end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal
