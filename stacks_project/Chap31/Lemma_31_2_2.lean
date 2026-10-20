/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Affine
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.2.2: associated primes of sections on an affine open map to associated points. -/
@[stacks 02OK] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints.fromSpec_mem_of_mem_associatedPrimesOfModule_sections :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
      (hp : p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U))),
      hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)

/- The converse for finitely generated primes. -/
#check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints.mem_associatedPrimesOfModule_sections_of_fromSpec_mem_of_fg :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
      (hx : hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)
      (hfg : p.asIdeal.FG),
      p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)))

/- The equivalence on a locally Noetherian scheme. -/
#check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints.mem_sections_iff_fromSpec_mem :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : IsAffineOpen U) [IsLocallyNoetherian X]
      (p : PrimeSpectrum (Γ(X, U))),
      p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)) ↔
        hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)
