module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Locally of finite presentation for morphisms of algebraic stacks

Typed compatibility checks for local finite presentation and its smooth
algebraic-space presentation characterization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    LocallyOfFinitePresentation f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFinitePresentation h)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    LocallyOfFinitePresentation (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f],
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFinitePresentation f],
    LocallyOfFinitePresentation (AlgebraicSpace.toGroupoids.map f))
