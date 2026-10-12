/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Cokernel

/-!
# Closed-Fiber Injectivity over Essentially Finite-Type Algebras

This module records consequences of closed-fiber injectivity for finite modules
over essentially finite-type local algebras, including the Noetherian case.
-/

@[expose] public section

universe u v w x

namespace LinearMap.ClosedFiber

/-- Over a Noetherian local base, a linear map with injective closed fiber into
a flat module is universally injective when its domain is finite over an
essentially finite-type local algebra. -/
theorem universallyInjective_of_noetherian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    LinearMap.UniversallyInjective.{u, x, w, max u x w} u := sorry

/-- Under the Noetherian closed-fiber criterion, the domain of the linear map
is flat over the base ring. -/
theorem flat_domain_of_noetherian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A N := sorry

/-- A module finite over an essentially finite-type local algebra over a
Noetherian local ring is finitely presented over that algebra. -/
theorem finitePresentation_domain_of_noetherian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.FinitePresentation B N := sorry

/-- Over a local base, a linear map with injective closed fiber into a flat
module is universally injective when its domain is finite over an essentially
finite-type local algebra. -/
theorem universallyInjective_of_essFiniteType
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    LinearMap.UniversallyInjective.{u, x, w, max u x w} u := sorry

/-- Under the closed-fiber injectivity criterion for an essentially finite-type
local algebra, the finite domain is finitely presented over that algebra. -/
theorem finitePresentation_domain_of_essFiniteType
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.FinitePresentation B N := sorry

/-- Under the closed-fiber injectivity criterion for an essentially finite-type
local algebra, the finite domain is flat over the base ring. -/
theorem flat_domain_of_essFiniteType
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A N := sorry

end LinearMap.ClosedFiber
