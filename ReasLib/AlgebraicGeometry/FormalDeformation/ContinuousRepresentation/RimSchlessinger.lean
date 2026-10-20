/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for continuous representations

The cofibered category of discrete-continuous finite projective
`Γ`-representations satisfies the Rim-Schlessinger condition. Consequently each
residue-fibre slice is a deformation category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

namespace ContinuousRep

/-- The projection from discrete-continuous finite projective representations to
Artinian local algebras satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Γ Λ k) := sorry

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The residue-fibre slice at a finite-dimensional discrete-continuous
representation is a deformation category. -/
instance instIsDeformationCategory_deformation
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    IsDeformationCategory
      (Over.forget (ofResidue Γ Λ k ρ0 hρ0) ⋙ forget Γ Λ k) :=
  instIsDeformationCategory_overForget (forget Γ Λ k)
    (Fiber.mk (rfl : (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0 hρ0) =
      ArtinianLocalAlgCat.residue Λ k))

end ContinuousRep
