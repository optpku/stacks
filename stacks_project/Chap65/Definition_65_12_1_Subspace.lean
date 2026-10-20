/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Open, closed, and locally closed subspaces of algebraic spaces

An open, closed, or locally closed subspace of an algebraic space `F` is an algebraic
space over the same base together with an inclusion into `F` that is an open immersion,
closed immersion, or immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.ofι :
  ∀ {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F) [AlgebraicSpace.IsOpenImmersion ι],
    AlgebraicSpace.OpenSubspace F)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.spec :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} (U : AlgebraicSpace.OpenSubspace F),
    AlgebraicSpace.IsOpenImmersion U.ι ∧ Mono U.ι)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.id :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S), AlgebraicSpace.OpenSubspace F)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofι :
  ∀ {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F)
    [AlgebraicSpace.IsClosedImmersion ι], AlgebraicSpace.ClosedSubspace F)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.spec :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} (Z : AlgebraicSpace.ClosedSubspace F),
    AlgebraicSpace.IsClosedImmersion Z.ι ∧ Mono Z.ι)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.id :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S), AlgebraicSpace.ClosedSubspace F)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace.ofι :
  ∀ {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F)
    [AlgebraicSpace.IsImmersion ι], AlgebraicSpace.LocallyClosedSubspace F)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace.spec :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} (W : AlgebraicSpace.LocallyClosedSubspace F),
    AlgebraicSpace.IsImmersion W.ι ∧ Mono W.ι)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace.id :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S), AlgebraicSpace.LocallyClosedSubspace F)
