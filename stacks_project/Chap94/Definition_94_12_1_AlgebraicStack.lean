module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty

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

#check (AlgebraicGeometry.AlgebraicStack :
  ∀ {S : Scheme.{u}}, GroupoidsOver S → Prop)

namespace AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.slice :
  ∀ {S : Scheme.{u}} (U : Over S),
    AlgebraicStack (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.instIsStackInGroupoids :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p)

#check (AlgebraicGeometry.AlgebraicStack.ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    AlgebraicStack F.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    AlgebraicStack X ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
        relativelyRepresentableByAlgebraicSpaces
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ∧
          ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
            Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p)

#check (AlgebraicGeometry.AlgebraicStack.objectProperty :
  ∀ (S : Scheme.{u}),
    ObjectProperty (GroupoidsOver S))

#check (AlgebraicGeometry.AlgebraicStack.objectProperty_apply :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    objectProperty S X ↔ AlgebraicStack X)

#check (AlgebraicGeometry.AlgebraicStack.iff_exists_representable_atlas :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    AlgebraicStack X ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
        relativelyRepresentableByAlgebraicSpaces
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ∧
          ∃ (U : GroupoidsOver S) (p : U ⟶ X),
            FiberedCategoryOver.Groupoids.IsRepresentable U ∧
              Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p)

end AlgebraicStack

end AlgebraicGeometry
