/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap93.Example_93_7_1_Graded_algebras

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

namespace FiniteProjectiveGradedAlgebraCat

/-- Lemma 93.7.2 (1): Example 93.7.1 satisfies the Rim-Schlessinger condition (RS),
recorded as `HasRimSchlessinger forget` for the projection `p : F ⥤ C_Λ`. -/
@[stacks 0DVY]
instance instHasRimSchlessinger_forget :
    HasRimSchlessinger (forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) :=
  sorry

-- `IsDeformationCategory` extends a parallel `IsPredeformationCategory` owner that
-- cannot be imported beside `Example_93_7_1_Graded_algebras_Category`. The source claim that
-- `Def_P` is a deformation category is the in-scope conjunction of predeformation
-- and (RS) on the slice projection.

/-- Lemma 93.7.2 (2): in particular, for any graded `k`-algebra `P` with finite projective
pieces, the slice projection of `deformationCategory P` is a deformation category. -/
@[stacks 0DVY]
theorem isDeformationCategory_deformationCategory (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget) ∧
      HasRimSchlessinger (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget) :=
  sorry

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationCategory
    (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget) := sorry

/-- The slice projection of `Def_P` satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_deformationCategory (P : FiniteProjectiveGradedAlgebra k) :
    HasRimSchlessinger
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget) := sorry

end FiniteProjectiveGradedAlgebraCat
