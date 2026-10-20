/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.SupportDim

/-!
# Modules with support of local dimension at most one

This file records consequences of the presence of a nonclosed point in the support of a finite
module whose support has dimension at most one.
-/

@[expose] public section

universe u v

namespace Module

/-- A nonclosed point in the support of a finite module of support dimension at most one forces
the support dimension to equal one. -/
theorem supportDim_eq_one_of_mem_ne_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : supportDim R M ≤ 1) (q : PrimeSpectrum R) (hq_mem : q ∈ support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) :
    supportDim R M = 1 := sorry

/-- A nonclosed point in the support of a finite module of support dimension at most one is a
minimal point of that support. -/
theorem minimal_of_mem_support_of_ne_closedPoint_of_supportDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : supportDim R M ≤ 1) (q : PrimeSpectrum R) (hq_mem : q ∈ support R M)
    (hq_ne_closedPoint : q ≠ IsLocalRing.closedPoint R) :
    Minimal (· ∈ support R M) q := sorry

end Module
