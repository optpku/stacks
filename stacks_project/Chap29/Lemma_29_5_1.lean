/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 29.5.1: for a quasi-coherent module sheaf on a scheme and an affine open, a prime of the
section ring supports the module of sections exactly when the corresponding point supports the
sheaf. -/
@[stacks 056I] #check
  (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_fromSpec_mem_support :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))),
      p ∈ Module.support (Γ(X, U)) (Γ(ℱ, U)) ↔
        hU.fromSpec p ∈ AlgebraicGeometry.RingedSpace.moduleSupport ℱ)
