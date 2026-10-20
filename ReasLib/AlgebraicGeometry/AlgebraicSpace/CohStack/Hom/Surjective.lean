/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.FieldValuedPoint

/-!
# Surjective morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is surjective if every field-valued point of `Y` is
equivalent to the image under `f` of some field-valued point of `X`, so that `|f|` is
surjective. Equivalence allows passing to a common field extension. -/
@[stacks 04ZS, mk_iff]
class Surjective {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- Every field-valued point of the target is equivalent to the image of a field-valued
  point of the source. -/
  exists_equivalent_map :
    ∀ q : FieldValuedPoint Y, ∃ p : FieldValuedPoint X, (p.map f).Equivalent q

namespace Surjective

/-- On morphisms of algebraic spaces, surjectivity of the associated groupoid
fibration morphism is surjectivity on the points of the algebraic spaces. -/
theorem toGroupoids_iff {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V) :
    Surjective (AlgebraicGeometry.GroupScheme.Classifying.toGroupoids.map h) ↔
      AlgebraicSpace.Surjective h :=
  sorry

/-- Every target field-valued point of a surjective morphism is equivalent to
the image of a source field-valued point. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Surjective f] (q : FieldValuedPoint Y) :
    ∃ p : FieldValuedPoint X, (p.map f).Equivalent q :=
  Surjective.exists_equivalent_map q

/-- The identity 1-morphism of a category fibred in groupoids is surjective. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Surjective (𝟙 X) :=
  sorry

/-- A composition of surjective 1-morphisms is surjective. -/
instance comp {S : Scheme.{u}}
    {X Y Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
