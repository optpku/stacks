/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction

/-!
# Formally smooth morphisms of algebraic stacks

A morphism of algebraic stacks is formally smooth when it is formally smooth
on objects as a 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is formally smooth if it is
formally smooth on objects as a 1-morphism of categories fibred in groupoids. -/
@[mk_iff]
class FormallySmooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Groupoids.Hom.FormallySmoothOnObjects f

namespace FormallySmooth

/-- The identity morphism of an algebraic stack is formally smooth. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    FormallySmooth (𝟙 X) :=
  sorry

/-- A morphism of algebraic stacks that is formally smooth on objects is
formally smooth. -/
instance of_onObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.FormallySmoothOnObjects f] : FormallySmooth f :=
  sorry

/-- A formally smooth morphism of algebraic stacks is formally smooth on
objects as a 1-morphism of categories fibred in groupoids. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f] :
    Groupoids.Hom.FormallySmoothOnObjects f :=
  sorry

/-- A morphism of algebraic stacks is formally smooth if and only if every
first-order affine thickening square, with its chosen comparison isomorphism,
has a nonempty category of compatible dotted arrows. -/
@[stacks 0DNY]
theorem iff_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    FormallySmooth f ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
        (i : T ⟶ T') [IsFirstOrderThickening i.left]
        (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
        (γ : overMap i ≫ y ≅ x ≫ f),
        Nonempty (DottedArrow
          (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
            Bicategory.PseudoPullbackCone y f)) :=
  sorry

/-- A formally smooth morphism of algebraic stacks has a nonempty category of
dotted arrows on every first-order affine thickening square. -/
theorem nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f]
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left]
    (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
    (γ : overMap i ≫ y ≅ x ≫ f) :
    Nonempty (DottedArrow
      (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
        Bicategory.PseudoPullbackCone y f)) :=
  sorry

/-- A morphism of algebraic stacks is formally smooth if every first-order
affine thickening square has a nonempty category of dotted arrows. -/
theorem of_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
      (i : T ⟶ T') [IsFirstOrderThickening i.left]
      (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
      (γ : overMap i ≫ y ≅ x ≫ f),
      Nonempty (DottedArrow
        (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
          Bicategory.PseudoPullbackCone y f))) :
    FormallySmooth f :=
  sorry


end FormallySmooth

end AlgebraicGeometry.AlgebraicStack
