module

public import ReasLib.Algebra.Module.FinitePresentation.ValuationRing
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Closed-fiber criteria over valuation rings

This file records injectivity and flat-cokernel criteria for finite modules over local algebras
essentially of finite type over a valuation ring.
-/

@[expose] public section

universe u v w x

namespace LinearMap

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [IsLocalRing B]
variable [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
variable {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
variable [Module A N] [IsScalarTower A B N]
variable {M : Type x} [AddCommGroup M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M] [Module.Flat A M]

/-- A linear map between finite modules over a local algebra essentially of finite type over a
valuation ring is injective if its reduction modulo the maximal ideal is injective. -/
@[stacks 0GSG]
theorem injective_of_finite_essFiniteTypeLocalValuationRing
    (u : N →ₗ[B] M)
    (hbar : Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Function.Injective u := sorry

/-- If a map between finite modules over a local algebra essentially of finite type over a
valuation ring is injective modulo the maximal ideal and its target is flat, then its cokernel is
flat over the valuation ring. -/
@[stacks 0GSG]
theorem flat_quotient_range_of_finite_essFiniteTypeLocalValuationRing
    (u : N →ₗ[B] M)
    (hbar : Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A (M ⧸ LinearMap.range u) := sorry

end

end LinearMap

namespace LinearMap.ClosedFiber

/-- Over a valuation ring, closed-fiber injectivity into a flat module forces the domain to be
flat over the base ring. -/
theorem flat_domain_of_valuationRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A N := sorry

/-- Over a valuation ring, a linear map with injective closed fiber into a flat module is
universally injective when its domain is finite over an essentially finite-type local algebra. -/
theorem universallyInjective_of_valuationRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    LinearMap.UniversallyInjective.{u, x, w, max u x w} u := sorry

/-- Over a valuation ring, the domain in the closed-fiber criterion is finitely presented over
the essentially finite-type local algebra. -/
theorem finitePresentation_domain_of_valuationRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.FinitePresentation B N := sorry

end LinearMap.ClosedFiber
