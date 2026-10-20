/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for finite projective graded algebras

Example 93.7.1 satisfies (RS), so each residue-fibre slice `Def_P` is a deformation
category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.7.2
Example 93.7.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DVY]
#check (FiniteProjectiveGradedAlgebraCat.instHasRimSchlessinger_forget :
  HasRimSchlessinger
    (FiniteProjectiveGradedAlgebraCat.forget :
      FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k))

/- In particular, the residue-fibre slice at any graded `k`-algebra with
finite-dimensional homogeneous pieces is a deformation category. -/
#check (FiniteProjectiveGradedAlgebraCat.instIsDeformationCategory_deformationCategory :
  ∀ P : FiniteProjectiveGradedAlgebra k,
    IsDeformationCategory
      (Over.forget
        (Fiber.fiberInclusion.obj (FiniteProjectiveGradedAlgebraCat.residueObj Λ P)) ⋙
        FiniteProjectiveGradedAlgebraCat.forget))
