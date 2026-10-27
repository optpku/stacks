/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Construction

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
# Construction computations for left-leg diagonal squares

Component and projection formulas for the explicit construction layer.
-/

/-- The left endpoint component of the left-leg cospan transformation is `P.fst`. -/
@[simp]
theorem transform.left (P : PseudoPullbackCone f g) :
    (transform P).left = P.fst := by
  rfl

/-- The right endpoint component of the left-leg cospan transformation is `P.fst`. -/
@[simp]
theorem transform.right (P : PseudoPullbackCone f g) :
    (transform P).right = P.fst := by
  rfl

/-- The base component of the left-leg cospan transformation is `g`. -/
@[simp]
theorem transform.base (P : PseudoPullbackCone f g) :
    (transform P).base = g := by
  rfl

/-- The left generating comparison of the left-leg transformation is `P.iso`. -/
@[simp]
theorem transform.leftIso (P : PseudoPullbackCone f g) :
    (transform P).leftIso = P.iso := by
  rfl

/-- The right generating comparison of the left-leg transformation is `P.iso`. -/
@[simp]
theorem transform.rightIso (P : PseudoPullbackCone f g) :
    (transform P).rightIso = P.iso := by
  rfl

/-- The induced apex map is the universal map attached to `transform P`. -/
@[simp]
theorem map.eq_mapCospan (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    map P Q R = PseudoPullbackCone.mapCospan Q R (transform P) := by
  rfl

/-- The source relative diagonal is the universal lift of the diagonal cone on `P.snd`. -/
@[simp]
theorem sourceDiagonal.eq_lift (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    sourceDiagonal P Q =
      PseudoPullbackCone.lift (PseudoPullbackCone.diagonal P.snd) Q := by
  rfl

/-- The target relative diagonal is the universal lift of the diagonal cone on `f`. -/
@[simp]
theorem targetDiagonal.eq_lift (R : PseudoPullbackCone f f) [R.IsBilimit] :
    targetDiagonal R =
      PseudoPullbackCone.lift (PseudoPullbackCone.diagonal f) R := by
  rfl

/-- The first source-diagonal projection comparison is the corresponding lift comparison. -/
@[simp]
theorem sourceDiagonal.fstIso.eq_lift (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    sourceDiagonal.fstIso P Q =
      PseudoPullbackCone.lift.fstIso (PseudoPullbackCone.diagonal P.snd) Q := by
  rfl

/-- The second source-diagonal projection comparison is the corresponding lift comparison. -/
@[simp]
theorem sourceDiagonal.sndIso.eq_lift (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) [Q.IsBilimit] :
    sourceDiagonal.sndIso P Q =
      PseudoPullbackCone.lift.sndIso (PseudoPullbackCone.diagonal P.snd) Q := by
  rfl

/-- The first target-diagonal projection comparison is the corresponding lift comparison. -/
@[simp]
theorem targetDiagonal.fstIso.eq_lift
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    targetDiagonal.fstIso R =
      PseudoPullbackCone.lift.fstIso (PseudoPullbackCone.diagonal f) R := by
  rfl

/-- The second target-diagonal projection comparison is the corresponding lift comparison. -/
@[simp]
theorem targetDiagonal.sndIso.eq_lift
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    targetDiagonal.sndIso R =
      PseudoPullbackCone.lift.sndIso (PseudoPullbackCone.diagonal f) R := by
  rfl

/-- The apex of the common cone is the apex of `P`. -/
@[simp]
theorem cone.pt (P : PseudoPullbackCone f g) : (cone P).pt = P.pt := by
  rfl

/-- The first projection of the common cone is `P.fst`. -/
@[simp]
theorem cone.fst (P : PseudoPullbackCone f g) : (cone P).fst = P.fst := by
  rfl

/-- The second projection of the common cone is `P.fst`. -/
@[simp]
theorem cone.snd (P : PseudoPullbackCone f g) : (cone P).snd = P.fst := by
  rfl

/-- The comparison of the common cone is the identity isomorphism. -/
@[simp]
theorem cone.iso (P : PseudoPullbackCone f g) :
    (cone P).iso = Iso.refl (P.fst ≫ f) := by
  rfl


end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

