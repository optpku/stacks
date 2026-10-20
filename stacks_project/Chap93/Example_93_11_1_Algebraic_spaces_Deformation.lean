/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Deformation

/-!
# Residue object and deformation category of an algebraic space

The object `x0 = (k, X)` of the residue fibre of `FlatAlgebraicSpaceCat.forget`,
and the slice `Def_X = F_{x0}`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

#check (FlatAlgebraicSpaceCat.deformation Λ k X : Type (u + 1))
