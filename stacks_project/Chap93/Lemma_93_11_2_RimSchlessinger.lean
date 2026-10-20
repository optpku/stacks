/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.RimSchlessinger

/-!
# Rim-Schlessinger condition for algebraic spaces

The cofibered category `F` of pairs `(A, X)` from Example 93.11.1 satisfies
(RS). Consequently each residue-fibre slice `Def_X` is a deformation
category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

#check (FlatAlgebraicSpaceCat.deformationForget Λ k X :
  FlatAlgebraicSpaceCat.deformation Λ k X ⥤ ArtinianLocalAlgCat Λ k)

#check (FlatAlgebraicSpaceCat.deformationForget_eq Λ k X :
  FlatAlgebraicSpaceCat.deformationForget Λ k X =
    Over.forget (Fiber.fiberInclusion.obj (FlatAlgebraicSpaceCat.residueObj Λ k X)) ⋙
      FlatAlgebraicSpaceCat.forget Λ k)

#check (FlatAlgebraicSpaceCat.instHasRimSchlessinger_forget Λ k :
  HasRimSchlessinger (FlatAlgebraicSpaceCat.forget Λ k))

#check (FlatAlgebraicSpaceCat.instIsDeformationCategory_deformationForget Λ k X :
  IsDeformationCategory (FlatAlgebraicSpaceCat.deformationForget Λ k X))
