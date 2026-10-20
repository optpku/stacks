/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 65.12.1 (1): a morphism of algebraic spaces over a scheme `S` is an
open immersion if it is representable and an open immersion in the sense of
Definition 65.5.1. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

/- Definition 65.12.1 (2): an open subspace of an algebraic space `F` over `S` is a
subfunctor `F' ⊂ F` such that `F'` is an algebraic space and `F' ⟶ F` is an open
immersion. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))

/- Definition 65.12.1 (3): a morphism of algebraic spaces over a scheme `S` is a
closed immersion if it is representable and a closed immersion in the sense of
Definition 65.5.1. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

/- Definition 65.12.1 (4): a closed subspace of an algebraic space `F` over `S` is a
subfunctor `F' ⊂ F` such that `F'` is an algebraic space and `F' ⟶ F` is a closed
immersion. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))

/- Definition 65.12.1 (5): a morphism of algebraic spaces over a scheme `S` is an
immersion if it is representable and an immersion in the sense of Definition 65.5.1. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.IsImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

/- Definition 65.12.1 (6): a locally closed subspace of an algebraic space `F` over `S`
is a subfunctor `F' ⊂ F` such that `F'` is an algebraic space and `F' ⟶ F` is an
immersion. -/
@[stacks 02YU] #check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))
