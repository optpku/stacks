/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Cokernel

/-!
# Closed-Fiber Injectivity over Henselian Local Rings

This module records consequences of closed-fiber injectivity over a Henselian
local base ring.
-/

@[expose] public section

universe u v w x

namespace LinearMap.ClosedFiber

/-- Over a Henselian local base, closed-fiber injectivity into a flat module
forces the domain to be flat over the base ring. -/
theorem flat_domain_of_henselian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.Flat A N := sorry

/-- Over a Henselian local base, a linear map with injective closed fiber into
a flat module is universally injective when its domain is finite over an
essentially finite-type local algebra. -/
theorem universallyInjective_of_henselian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    LinearMap.UniversallyInjective.{u, x, w, max u x w} u := sorry

/-- Over a Henselian local base, the domain in the closed-fiber criterion is
finitely presented over the essentially finite-type local algebra. -/
theorem finitePresentation_domain_of_henselian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N] (u : N →ₗ[A] M)
    (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))) :
    Module.FinitePresentation B N := sorry

end LinearMap.ClosedFiber
