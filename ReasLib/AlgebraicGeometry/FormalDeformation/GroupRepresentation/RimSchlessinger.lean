/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for representations of a group

The cofibered category of finite projective `Γ`-representations satisfies the
Rim-Schlessinger condition. Consequently each residue-fibre slice is a
deformation category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]

namespace GroupRepCat

/-- The projection from finite projective representations to Artinian local
algebras satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Γ Λ k) := sorry

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The residue-fibre slice `Def_{V, ρ0}` is a deformation category. -/
instance instIsDeformationCategory_deformation
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    IsDeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0)) ⋙ forget Γ Λ k) :=
  instIsDeformationCategory_overForget (forget Γ Λ k) (residueObj Γ Λ k ρ0)

end GroupRepCat
