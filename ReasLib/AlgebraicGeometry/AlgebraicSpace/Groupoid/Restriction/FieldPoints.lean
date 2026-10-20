/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Field
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField

/-!
# Algebraically closed lifts of arrow points

This module lifts an arbitrary point of the arrow space of a groupoid in
algebraic spaces on a field after restriction to an algebraically closed
extension of that field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Every point of the arrow space of a groupoid in algebraic spaces on a field
lifts after restriction to an algebraically closed field extension, with both
endpoints automorphisms of `Spec(k')`. -/
theorem existsAlgebraicallyClosedArrowLift
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    (r : Points G.R.left) :
    ∃ (k' : Type u) (_ : Field k') (ι : k →+* k') (_ : IsAlgClosed k'),
      let g := G.fieldRestrictionOfHom (IsOnField.objectSpaceIso G σ) ι
      let G' := G.pullback g
      let φ := G.pullbackHom g
      ∃ (r' : G'.U.left ⟶ G'.R.left),
        Points.map φ.arrow.left
            (Points.mk (FieldValuedPoint.of k'
              (Spec.map (CommRingCat.ofHom ι) ≫ σ) r')) = r ∧
          IsIso (r' ≫ G'.s.left) ∧ IsIso (r' ≫ G'.t.left) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
