/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.4.2 (1): an algebraic stack over S is DM over S if the
structure morphism is DM. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsDMOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (2): an algebraic stack over S is quasi-DM over S if the
structure morphism is quasi-DM. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDMOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (3): an algebraic stack over S is separated over S if the
structure morphism is separated. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsSeparatedOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (4): an algebraic stack over S is quasi-separated over S
if the structure morphism is quasi-separated. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparatedOver :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (5): an algebraic stack is DM if it is DM over Spec ℤ
after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsDM :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (6): an algebraic stack is quasi-DM if it is quasi-DM
over Spec ℤ after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDM :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (7): an algebraic stack is separated if it is separated
over Spec ℤ after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsSeparated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

/- Definition 101.4.2 (8): an algebraic stack is quasi-separated if it is
quasi-separated over Spec ℤ after viewing via Algebraic Stacks,
Definition 94.19.2. -/
@[stacks 050D] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)
