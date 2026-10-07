module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_11
public import stacks_project.Chap93.Example_93_5_1_Representations_of_a_group

/-!
# Rim-Schlessinger condition for representations of a group

The cofibered category `F` of finite projective `Γ`-representations from
Example 93.5.1 satisfies (RS). Consequently each residue-fibre slice
`Def_{V, ρ0}` is a deformation category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]

namespace GroupRepCat

/-- Example 93.5.1 satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Γ Λ k) := sorry

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The residue-fibre slice `Def_{V, ρ0}` is a deformation category. -/
instance instIsDeformationCategory_deformation
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    IsDeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0)) ⋙ forget Γ Λ k) :=
  instIsDeformationCategory_overForget (forget Γ Λ k) (residueObj Γ Λ k ρ0)

end GroupRepCat
