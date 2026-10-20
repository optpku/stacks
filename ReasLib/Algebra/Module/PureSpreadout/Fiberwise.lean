/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PureSpreadout.AtPrime
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
public import ReasLib.RingTheory.Module.Support.LinearMap

@[expose] public section

universe u v w x z

namespace LinearMap

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B) {N : Type w} [AddCommGroup N]
variable {M : Type x} [AddCommGroup M]

/-- For a finitely presented algebra, a linear map from a finitely presented module over a
localization is universally injective over the base if its source and target are flat over the
base and it is injective on every residue-field fiber. -/
theorem universallyInjective_of_fiberInjective
    [Module (Localization S) N] [Module B N] [Module A N]
    [IsScalarTower B (Localization S) N] [IsScalarTower A B N]
    [Module.FinitePresentation (Localization S) N] [Module A M]
    (hAB : (algebraMap A B).FinitePresentation)
    [Module.Flat A N] [Module.Flat A M]
    (u : N →ₗ[A] M) (hu : ∀ p : PrimeSpectrum A, u.IsFiberInjectiveAt p) :
    UniversallyInjective.{u, w, x, max u v w x z} u := sorry

end LinearMap
