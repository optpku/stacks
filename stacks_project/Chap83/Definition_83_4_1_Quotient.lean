/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CategoricalQuotient
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Categorical quotients in schemes

This file records the schemes specialization of the generic categorical quotient
API for pre-relations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- The full subcategory of algebraic spaces over `B` that are schemes. -/
def isScheme {S : Scheme.{u}} {B : AlgebraicSpace S} : ObjectProperty (Over B) :=
  fun X ↦ IsScheme X.left

/-- Membership in `isScheme` is the property that the underlying algebraic space is a
scheme. -/
theorem isScheme_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    isScheme X ↔ IsScheme X.left :=
  Iff.rfl

/-- A morphism of algebraic spaces over `S` is a categorical quotient in schemes when it
is a categorical quotient in the full subcategory of schemes over `S`. -/
abbrev IsCategoricalQuotientInSchemes {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.IsCategoricalQuotientIn isScheme φ

/-- A categorical quotient in schemes is a categorical quotient in the full subcategory
of schemes over `S`. -/
theorem isCategoricalQuotientInSchemes_iff {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotientInSchemes φ ↔ P.IsCategoricalQuotientIn isScheme φ :=
  Iff.rfl

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
