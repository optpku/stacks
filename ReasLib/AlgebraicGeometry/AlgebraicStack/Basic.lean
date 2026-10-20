/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Algebraic stacks over a scheme

An algebraic stack over a scheme `S` is a category fibred in groupoids over
`(Sch/S)_fppf` that is a stack in groupoids, whose diagonal is representable by
algebraic spaces, and that admits a smooth surjective atlas from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An algebraic stack over a scheme `S` is a category fibred in groupoids over
`(Sch/S)_fppf` that is a stack in groupoids, whose diagonal is representable by
algebraic spaces, and that admits a scheme atlas which is surjective and
smooth. -/
class AlgebraicStack {S : Scheme.{u}} (X : GroupoidsOver S) : Prop where
  /-- The category is a stack in groupoids over the big fppf site of `S`. -/
  isStack : IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p
  /-- The diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces. -/
  representableDiagonal :
    relativelyRepresentableByAlgebraicSpaces (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)
  /-- There is a scheme `U` over `S` and a surjective smooth 1-morphism
  `GroupoidsOver.slice U ⟶ X`. -/
  existsSmoothSurjectiveAtlas :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p

namespace AlgebraicStack

/-- The canonical slice fibration of a scheme over `S` is an algebraic stack. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    AlgebraicStack (GroupoidsOver.slice U) := sorry

/-- An algebraic stack is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids {S : Scheme.{u}} (X : GroupoidsOver S)
    [h : AlgebraicStack X] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p :=
  h.isStack

/-- The groupoid fibration of an algebraic space is an algebraic stack. -/
instance ofAlgebraicSpace {S : Scheme.{u}} (F : AlgebraicSpace S) :
    AlgebraicStack F.toGroupoids := sorry

/-- Being an algebraic stack is equivalent to the three defining clauses: stack
in groupoids, diagonal representable by algebraic spaces, and a surjective
smooth scheme atlas. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    AlgebraicStack X ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
        relativelyRepresentableByAlgebraicSpaces
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ∧
          ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
            Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p := sorry

/-- The object property on categories fibred in groupoids over `Over S` selecting
algebraic stacks. -/
def objectProperty (S : Scheme.{u}) : ObjectProperty (GroupoidsOver S) :=
  fun X ↦ AlgebraicStack X

/-- The object property of algebraic stacks is the class `AlgebraicStack`. -/
theorem objectProperty_apply {S : Scheme.{u}} (X : GroupoidsOver S) :
    objectProperty S X ↔ AlgebraicStack X := sorry

/-- Equivalently, the atlas in the definition of an algebraic stack may be taken
to be a representable category fibred in groupoids, i.e. one equivalent to a
canonical slice. -/
theorem iff_exists_representable_atlas {S : Scheme.{u}} (X : GroupoidsOver S) :
    AlgebraicStack X ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
        relativelyRepresentableByAlgebraicSpaces
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ∧
          ∃ (U : GroupoidsOver S) (p : U ⟶ X),
            FiberedCategoryOver.Groupoids.IsRepresentable U ∧
              Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p := sorry

end AlgebraicStack

end AlgebraicGeometry

/-- An algebraic stack is a stack on the big fppf site of its base scheme. -/
instance AlgebraicGeometry.AlgebraicStack.instIsStackOnSite
    {S : AlgebraicGeometry.Scheme.{u}} (Y : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack Y] :
    CategoryTheory.IsStack.OnSite (AlgebraicGeometry.Scheme.fppfTopology.over S) Y.p :=
  CategoryTheory.IsStack.InGroupoids.toOnSite inferInstance
