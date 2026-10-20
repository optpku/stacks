/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Locally of finite type for morphisms of algebraic stacks

A morphism of algebraic stacks is locally of finite type when some smooth
algebraic-space presentation square with surjective source atlas has
locally-of-finite-type top arrow, parallel to `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.locallyOfFiniteType_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    LocallyOfFiniteType f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFiniteType h)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    LocallyOfFiniteType (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f],
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFiniteType f],
    LocallyOfFiniteType (AlgebraicSpace.toGroupoids.map f))

end AlgebraicGeometry.AlgebraicStack
