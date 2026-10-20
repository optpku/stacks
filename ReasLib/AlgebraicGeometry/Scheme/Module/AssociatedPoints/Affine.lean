/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints

/-!
# Associated points on affine opens

This file compares associated primes of sections on an affine open with associated points of a
quasi-coherent scheme module.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.associatedPoints

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- An associated prime of the sections of a quasi-coherent module on an affine open determines
an associated point of the module. -/
theorem fromSpec_mem_of_mem_associatedPrimesOfModule_sections
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hp : p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U))) :
    hU.fromSpec p ∈ associatedPoints ℱ := sorry

/-- If a prime of an affine section ring is finitely generated, association of its corresponding
point implies that the prime is associated to the module of sections. -/
theorem mem_associatedPrimesOfModule_sections_of_fromSpec_mem_of_fg
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hx : hU.fromSpec p ∈ associatedPoints ℱ) (hfg : p.asIdeal.FG) :
    p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- On a locally Noetherian scheme, a prime of an affine section ring is associated to the
sections of a quasi-coherent module exactly when its corresponding point is associated. -/
theorem mem_sections_iff_fromSpec_mem
    {U : X.Opens} (hU : IsAffineOpen U) [IsLocallyNoetherian X]
    (p : PrimeSpectrum (Γ(X, U))) :
    p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ associatedPoints ℱ := sorry

end AlgebraicGeometry.Scheme.Modules.associatedPoints
