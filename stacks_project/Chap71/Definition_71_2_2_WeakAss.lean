/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints

/-!
# Weakly associated points of modules on algebraic spaces

Weak association of module sheaves is tested at geometric stalks. The weakly
associated locus of an algebraic space agrees with that of its structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.weakAss :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → X.Modules → Set (Points X))
