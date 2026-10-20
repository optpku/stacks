/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra

/-!
# Flat-algebra deformation categories
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k P : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] [CommRing P] [Algebra k P]

#check (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)

#check (FlatAlgebraCat.deformationCategory_spec Λ k P :
  FlatAlgebraCat.deformationCategory Λ k P =
    Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)))
