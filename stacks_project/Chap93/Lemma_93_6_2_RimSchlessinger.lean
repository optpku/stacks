/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_11
public import stacks_project.Chap93.Example_93_6_1_Representations_of_a_topological_group

/-!
# Rim-Schlessinger condition for continuous representations

The cofibered category `F` of discrete-continuous finite projective
`Γ`-representations from Example 93.6.1 satisfies (RS). Consequently each
residue-fibre slice `Def_{V, ρ0}` is a deformation category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

namespace ContinuousRep

/-- Example 93.6.1 satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Γ Λ k) := sorry

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The residue-fibre slice `Def_{V, ρ0}` is a deformation category. -/
instance instIsDeformationCategory_deformation
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    IsDeformationCategory
      (Over.forget (ofResidue Γ Λ k ρ0 hρ0) ⋙ forget Γ Λ k) :=
  instIsDeformationCategory_overForget (forget Γ Λ k)
    (Fiber.mk (rfl : (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0 hρ0) =
      ArtinianLocalAlgCat.residue Λ k))

end ContinuousRep
