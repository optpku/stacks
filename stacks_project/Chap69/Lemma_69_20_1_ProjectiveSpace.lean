/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ofScheme :
  ℕ → (S : Scheme.{u}) → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace :
  ℕ → {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.toBase :
  (n : ℕ) → {S : Scheme.{u}} → (Y : AlgebraicSpace S) → ProjectiveSpace n Y ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.toOfScheme :
  (n : ℕ) → {S : Scheme.{u}} → (Y : AlgebraicSpace S) →
    ProjectiveSpace n Y ⟶ ofScheme n S)
