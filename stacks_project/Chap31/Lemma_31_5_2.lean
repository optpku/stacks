/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.5.2: for a quasicoherent module ℱ on a scheme X, a prime p of the
section ring of an affine open U is weakly associated to Γ(ℱ,U) if and only if
the corresponding point is weakly associated to ℱ. -/
@[stacks 056M] #check
  (AlgebraicGeometry.Scheme.Modules.mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))),
      p.asIdeal ∈ weaklyAssociatedPrimes (Γ(X, U)) (Γ(ℱ, U)) ↔
        hU.fromSpec p ∈ ℱ.weakAss)
