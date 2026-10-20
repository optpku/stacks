/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for continuous representations

Example 93.6.1 satisfies (RS), so `Def_{V, ρ0}` is a deformation category for
any finite-dimensional continuous representation
`ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
  (hρ0 : ContinuousRep.IsContinuousDiscrete ρ0)

/- Lemma 93.6.2 (1)
Example 93.6.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DVV]
#check (ContinuousRep.instHasRimSchlessinger_forget Γ Λ k :
  HasRimSchlessinger (ContinuousRep.forget Γ Λ k))

/- Lemma 93.6.2 (2)
In particular, `Def_{V, ρ0}` is a deformation category for any finite-dimensional
continuous representation `ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`. -/
@[stacks 0DVV]
#check (ContinuousRep.instIsDeformationCategory_deformation Γ Λ k ρ0 hρ0 :
  IsDeformationCategory
    (Over.forget (ContinuousRep.ofResidue Γ Λ k ρ0 hρ0) ⋙
      ContinuousRep.forget Γ Λ k))
