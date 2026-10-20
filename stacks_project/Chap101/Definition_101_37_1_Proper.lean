/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper

/-!
# Proper morphisms of algebraic stacks

A morphism of algebraic stacks is proper when it is separated, of finite
type, and universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Proper :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.proper_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Proper f ↔ Separated f ∧ FiniteType f ∧ UniversallyClosed f)

#check (AlgebraicGeometry.AlgebraicStack.Proper.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Proper f],
    Separated f ∧ FiniteType f ∧ UniversallyClosed f)

#check (AlgebraicGeometry.AlgebraicStack.Proper.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Proper (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Proper.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    Proper f)

#check (AlgebraicGeometry.AlgebraicStack.Proper.instOfSeparatedFiniteTypeUniversallyClosed :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Separated f] [FiniteType f] [UniversallyClosed f], Proper f)

#check (AlgebraicGeometry.AlgebraicStack.Proper.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Proper f], Proper (AlgebraicSpace.toGroupoids.map f))

end AlgebraicGeometry.AlgebraicStack
