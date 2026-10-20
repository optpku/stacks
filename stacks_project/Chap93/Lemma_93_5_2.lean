/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for representations of a group

Example 93.5.1 satisfies (RS), so `Def_{V, ρ0}` is a deformation category for
any finite-dimensional representation `ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)

/- Lemma 93.5.2 (1)
Example 93.5.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DVS]
#check (GroupRepCat.instHasRimSchlessinger_forget Γ Λ k :
  HasRimSchlessinger (GroupRepCat.forget Γ Λ k))

/- Lemma 93.5.2 (2)
In particular, `Def_{V, ρ0}` is a deformation category for any finite-dimensional
representation `ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`. -/
@[stacks 0DVS]
#check (GroupRepCat.instIsDeformationCategory_deformation Γ Λ k ρ0 :
  IsDeformationCategory
    (Over.forget (Fiber.fiberInclusion.obj (GroupRepCat.residueObj Γ Λ k ρ0)) ⋙
      GroupRepCat.forget Γ Λ k))
