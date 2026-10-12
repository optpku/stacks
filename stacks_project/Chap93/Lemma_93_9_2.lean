/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation
public import stacks_project.Chap90.Definition_90_16_8
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rim-Schlessinger condition for schemes

Example 93.9.1 satisfies (RS), so each residue-fibre slice `Def_X` is a
deformation category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- Lemma 93.9.2 (1)
Example 93.9.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DY8, instance]
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

/-- Lemma 93.9.2 (2)
In particular, `Def_X` is a deformation category for any scheme `X` over `k`. -/
@[stacks 0DY8, instance]
instance instIsDeformationCategory_deformationCategory (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    IsDeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) :=
  sorry

end FlatSchemeCat
