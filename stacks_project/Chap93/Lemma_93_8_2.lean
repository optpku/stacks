/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

/-!
# Rim-Schlessinger condition for flat algebras

Example 93.8.1 satisfies (RS), so each residue-fibre slice `Def_P` is a deformation
category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraCat

/-- Lemma 93.8.2 (1): Example 93.8.1 satisfies the Rim-Schlessinger condition (RS),
recorded as `HasRimSchlessinger forget` for the projection `p : F ⥤ C_Λ`. -/
@[stacks 0DY2]
instance instHasRimSchlessinger_forget :
    HasRimSchlessinger (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) := sorry

-- `IsDeformationCategory` extends a parallel `IsPredeformationCategory` owner that
-- cannot be imported beside `Example_93_8_1_Rings_Category`. The source claim that
-- `Def_P` is a deformation category is the in-scope conjunction of predeformation
-- and (RS) on the slice projection.

/-- Lemma 93.8.2 (2): in particular, for any `k`-algebra `P`, the slice projection of
`deformationCategory P` is a deformation category. -/
@[stacks 0DY2]
theorem isDeformationCategory_deformationCategory
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget) ∧
      HasRimSchlessinger (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget) := sorry

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationCategory
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget) := sorry

/-- The slice projection of `Def_P` satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_deformationCategory
    (P : Type u) [CommRing P] [Algebra k P] :
    HasRimSchlessinger
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget) := sorry

end FlatAlgebraCat
