/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback

/-!
# Fibres of points of algebraic spaces

A pair of morphisms of algebraic spaces determines, at a pair of points of the
targets, the set of points of the common source mapping to both.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

variable {S : Scheme.{u}} {W X Z : AlgebraicSpace S}

/-- The set of points of `W` mapping to a given pair of points along `p` and `q`. -/
def fibre (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z) : Set (Points W) :=
  { w | map p w = x ∧ map q w = z }

/-- Membership in the fibre is the pair of point-mapping equations. -/
theorem mem_fibre_iff (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z) (w : Points W) :
    w ∈ fibre p q x z ↔ map p w = x ∧ map q w = z :=
  sorry

/-- The fibre equals the set of points of `W` sent to `x` by `p` and to `z` by `q`. -/
theorem fibre_eq (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z) :
    fibre p q x z = { w | map p w = x ∧ map q w = z } :=
  sorry

/-- The fibre is the intersection of the corresponding singleton preimages. -/
theorem fibre_eq_inter (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z) :
    fibre p q x z = map p ⁻¹' {x} ∩ map q ⁻¹' {z} :=
  sorry

variable {Y : AlgebraicSpace S} {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}

/-- On a cartesian square, the fibre over a compatible pair is the fibre of the points
comparison. -/
theorem fibre_eq_pullbackComparison_preimage (h : IsPullback p q f g) (x : Points X)
    (z : Points Z) (hy : map f x = map g z) :
    fibre p q x z = pullbackComparison h ⁻¹' {⟨(x, z), hy⟩} :=
  sorry

/-- The fibre over a pair of points is nonempty if and only if the points have the same image
in the common target. -/
theorem nonempty_fibre_iff (h : IsPullback p q f g) (x : Points X) (z : Points Z) :
    (fibre p q x z).Nonempty ↔ map f x = map g z :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
