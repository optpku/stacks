/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.LocalAtTarget

/-!
# Local tests for universally closed morphisms of algebraic spaces

The scheme, affine, étale-atlas, and Zariski-cover tests are available from the
shared mathematical owner.
-/

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallScheme :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallAffine :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.existsEtaleOnTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.existsZariskiCover :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)
