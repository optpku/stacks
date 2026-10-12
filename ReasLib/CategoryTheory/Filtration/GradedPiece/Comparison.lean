/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons with Graded Pieces

This module owns the universal-property interface for identifying a graded piece of a filtered
object with another object.  It deliberately separates the concrete cokernel descent from the
proposition-level inverse and compatibility laws, so clients never need to construct a quotient
map from an unfinished global theorem.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredObject
namespace GradedPiece

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- The map out of a graded piece induced by a morphism from its filtration stage that kills the
next stage. -/
@[stacks 0121 "graded-piece quotient descent"]
noncomputable def desc (F : FilteredObject C) (p : ℤ) {X : C}
    (projection : F.stage p ⟶ X)
    (h_zero : F.succInclusion p ≫ projection = 0) :
    F.gradedPiece p ⟶ X :=
  cokernel.desc (F.succInclusion p) projection h_zero

/-- A comparison between a graded piece and an object, stated through its stage projection and
two-sided inverse data. -/
@[stacks 0121 "graded-piece comparison"]
structure Comparison (F : FilteredObject C) (p : ℤ) {X : C}
    (projection : F.stage p ⟶ X) (hom : F.gradedPiece p ⟶ X)
    (toQuotient : X ⟶ F.gradedPiece p) : Prop where
  /-- The forward comparison has the prescribed composite with the quotient projection. -/
  π_hom : cokernel.π (F.succInclusion p) ≫ hom = projection
  /-- The forward and backward comparisons compose to the identity on the graded piece. -/
  hom_comp_toQuotient : hom ≫ toQuotient = 𝟙 (F.gradedPiece p)
  /-- The backward and forward comparisons compose to the identity on the target. -/
  toQuotient_comp_hom : toQuotient ≫ hom = 𝟙 X

namespace Comparison

/-- The isomorphism encoded by a graded-piece comparison. -/
@[stacks 0121 "graded-piece comparison isomorphism"]
noncomputable def isoOf {F : FilteredObject C} {p : ℤ} {X : C}
    {projection : F.stage p ⟶ X} {hom : F.gradedPiece p ⟶ X}
    {toQuotient : X ⟶ F.gradedPiece p}
    (h : FilteredObject.GradedPiece.Comparison F p projection hom toQuotient) :
    F.gradedPiece p ≅ X where
  hom := hom
  inv := toQuotient
  hom_inv_id := h.hom_comp_toQuotient
  inv_hom_id := h.toQuotient_comp_hom

/-- The forward map in a graded-piece comparison is the universal cokernel descent when the
given stage projection is known to kill the next stage. -/
@[stacks 0121 "graded-piece comparison descent"]
theorem hom_eq_desc {F : FilteredObject C} {p : ℤ} {X : C}
    {projection : F.stage p ⟶ X} {hom : F.gradedPiece p ⟶ X}
    {toQuotient : X ⟶ F.gradedPiece p}
    (h : FilteredObject.GradedPiece.Comparison F p projection hom toQuotient)
    (h_zero : F.succInclusion p ≫ projection = 0) :
    hom = desc F p projection h_zero := sorry

end Comparison

end GradedPiece
end FilteredObject
end CategoryTheory
