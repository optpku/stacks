/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorAmplitude

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The degree-zero cohomology-section functor of a pseudo-coherent derived module is affine and
finitely presented when all scheme pullbacks have vanishing degree-minus-one cohomology. -/
theorem cohomologyZeroFunctor_isAffineFinitePresentation (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ σ : SchemeOver B,
      IsZero (cohomologySheaf (pullbackOver K σ) (-1))) :
    IsAffineFinitePresentationOver (cohomologyZeroFunctor K) := sorry

/-- A pseudo-coherent derived module is perfect when every scheme pullback has vanishing negative
cohomology. -/
theorem isPerfect_of_negativePullbackCohomology (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    IsPerfect K := sorry

/-- A pseudo-coherent derived module whose scheme pullbacks have vanishing negative cohomology has
Tor-amplitude in `[0, b]` for some `b ≥ 0` on each affine étale scheme over the base. -/
theorem exists_hasTorAmplitudeIn_of_negativePullbackCohomology
    (K : ModuleDerived B) (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    ∀ (σ : SchemeOver B) [Etale σ.hom] [AlgebraicGeometry.IsAffine σ.left.left],
      ∃ b : ℤ, 0 ≤ b ∧ HasTorAmplitudeIn (pullbackOver K σ) 0 b := sorry

/-- The derived degree-zero section functor of a pseudo-coherent derived module is affine and
finitely presented when every scheme pullback has vanishing negative cohomology. -/
theorem derivedZeroFunctor_isAffineFinitePresentation (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    IsAffineFinitePresentationOver (derivedZeroFunctor K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
