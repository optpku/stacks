module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap93.Example_93_6_1_Representations_of_a_topological_group_Category

/-!
# Deformation category of a continuous representation

The residue object `x0 = (k, V, ρ0)` of a finite-dimensional continuous
`k`-representation, and the slice `Def_{V, ρ0} = F_{x0}`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ContinuousRep

variable {Γ Λ k : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/-- Restriction of scalars along the residue identification, so a `k`-module is a
module over the residue object of `ArtinianLocalAlgCat`. -/
instance instModuleResidueCarrier {V : Type u} [AddCommGroup V] [Module k V] :
    Module (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (Module k V)

section Residue

variable (Γ Λ k)

/-- The residue object `x0 = (k, V, ρ0)` of a finite-dimensional continuous
`k`-representation. -/
def ofResidue {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    ContinuousRep Γ Λ k where
  base := ArtinianLocalAlgCat.residue Λ k
  module := V
  finiteProjective := sorry
  ρ := ρ0
  continuous_ρ := hρ0

/-- The forgetful image of `ofResidue ρ0` is the residue object of `ArtinianLocalAlgCat`. -/
theorem ofResidue_base {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0 hρ0) = ArtinianLocalAlgCat.residue Λ k := sorry

/-- The deformation category `Def_{V, ρ0}` is the slice `F_{x0}` at
`x0 = (k, V, ρ0)`. -/
abbrev deformationCategory {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :=
  Over (ofResidue Γ Λ k ρ0 hρ0)

/-- `deformationCategory ρ0` is the Over-slice of `ofResidue ρ0`. -/
theorem deformationCategory_spec {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    deformationCategory Γ Λ k ρ0 hρ0 = Over (ofResidue Γ Λ k ρ0 hρ0) := sorry

end Residue

end ContinuousRep
