module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.EssFiniteType

/-!
# Closed-Fiber Criteria for Linear Maps after Restriction of Scalars

This module records closed-fiber consequences for a linear map over an essentially
finite-type local algebra, viewed as a linear map over the base ring.
-/

@[expose] public section

universe u v w x

namespace LinearMap.ClosedFiber

/-- A linear map over an essentially finite-type local algebra is universally injective
over the base ring if its target is flat and its closed-fiber map is injective. -/
theorem universallyInjective_restrictScalars
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[B] M)
    (hbar : Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    LinearMap.UniversallyInjective.{u, x, w, max u x w} (u.restrictScalars A) := sorry

/-- Under the injective closed-fiber criterion, the finite domain of a linear map over an
essentially finite-type local algebra is finitely presented over that algebra. -/
theorem finitePresentation_domain_restrictScalars
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[B] M)
    (hbar : Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.FinitePresentation B N := sorry

/-- Under the injective closed-fiber criterion, the finite domain of a linear map over an
essentially finite-type local algebra is flat over the base ring. -/
theorem flat_domain_restrictScalars
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[B] M)
    (hbar : Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A N := sorry

end LinearMap.ClosedFiber
