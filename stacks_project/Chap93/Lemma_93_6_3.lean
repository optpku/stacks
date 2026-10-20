/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.Tangent
import StacksCheckRecall

/-!
# Tangent space and infinitesimal automorphisms of continuous representations
-/

open CategoryTheory Functor

universe u

/- Lemma 93.6.3
The tangent space identifies with continuous first cohomology of the conjugation
representation, and infinitesimal automorphisms identify with degree-zero cohomology.
The infinitesimal space is finite-dimensional; the tangent space is finite-dimensional
when the topological group is topologically finitely generated. -/
@[stacks 0DVW] #check (ContinuousRep.tangent_infinitesimal_comparison :
  ∀ (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : ContinuousRep.IsContinuousDiscrete ρ0),
    Function.Bijective (ContinuousRep.tangentToH1 Γ Λ k ρ0 hρ0) ∧
    Function.Bijective (ContinuousRep.h0ToInfAut Γ Λ k ρ0 hρ0) ∧
    FiniteDimensional k (ContinuousRep.infinitesimalSpace Γ Λ k ρ0 hρ0) ∧
    (TopologicalGroup.IsFinitelyGenerated Γ →
      FiniteDimensional k (tangentSpaceAt (ContinuousRep.forget Γ Λ k)
        (ContinuousRep.residueObj Γ Λ k ρ0 hρ0))))
