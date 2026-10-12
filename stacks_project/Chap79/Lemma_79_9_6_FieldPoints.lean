/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap79.Lemma_79_9_6_Restriction

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
      ∃ (r' : G'.U ⟶ G'.R),
        Points.map φ.arrow.left
            (Points.mk (FieldValuedPoint.of k'
              (Spec.map (CommRingCat.ofHom ι) ≫ σ) r'.left)) = r ∧
          IsIso (r' ≫ G'.s) ∧ IsIso (r' ≫ G'.t) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
