/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.Deformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for finite projective modules

Finite projective modules over Artinian local algebras satisfy the
Rim-Schlessinger condition, and their residue-fibre slices are deformation categories.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- The projection of finite projective modules over Artinian local algebras
satisfies the Rim-Schlessinger condition. -/
@[stacks 0DVP]
instance instHasRimSchlessinger : HasRimSchlessinger (groupoids Λ k).p := sorry

/-- The residue-fibre slice at a finite-dimensional vector space is a
deformation category. -/
@[stacks 0DVP]
instance instIsDeformationCategory_deformation
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    IsDeformationCategory
      (deformation V :
          CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
            (ArtinianLocalAlgCat Λ k)).p :=
  instIsDeformationCategory_overForget (groupoids Λ k).p (residueObject V)

end ArtinianLocalAlgCat.FiniteProjective
