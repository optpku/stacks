/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.Tangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Hulls and prorepresentability of continuous representation deformations

The functor of isomorphism classes of deformations of a finite-dimensional continuous
representation of a topologically finitely generated group has a hull over a classical base.
It is prorepresentable when the invariant endomorphism space has dimension one.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

namespace ContinuousRep

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The functor of isomorphism classes of continuous deformations of the residue representation `ρ0`. -/
abbrev isoClassFunctor (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Γ Λ k ρ0 hρ0)

/-- Over a classical base, the functor of isomorphism classes of deformations of a
finite-dimensional continuous representation of a topologically finitely generated group
has a hull: a smooth map from a prorepresentable functor that is bijective on dual-number
points. -/
theorem exists_isHull_isoClass (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (hΓ : TopologicalGroup.IsFinitelyGenerated Γ)
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Γ Λ k ρ0 hρ0,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

/-- Over a classical base, the functor of isomorphism classes of deformations of a
finite-dimensional continuous representation of a topologically finitely generated group
is prorepresentable if its invariant endomorphism space has dimension one. -/
theorem isProrepresentable_isoClass (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (hΓ : TopologicalGroup.IsFinitelyGenerated Γ)
    [ArtinianLocalAlgCat.IsClassical Λ k]
    (hH0 : Module.finrank k (endRepresentation Γ Λ k ρ0 hρ0).invariants = 1) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Γ Λ k ρ0 hρ0) :=
  sorry

end ContinuousRep
