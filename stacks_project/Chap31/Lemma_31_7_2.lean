/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.Affine
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.7.2: an affine-section prime in the relative assassin determines a point in the
scheme-theoretic relative assassin. -/
@[stacks 0CU5] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.fromSpec_mem_of_mem_sections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U)))
      (hp : p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin.sections f ℱ U V e),
      hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)

#check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.mem_sections_iff_fromSpec_mem_of_isLocallyNoetherian_fibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V) (hfib : ∀ s : S, IsLocallyNoetherian (Scheme.Hom.fiber f s))
      (p : PrimeSpectrum (Γ(X, U))),
      p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin.sections f ℱ U V e ↔
        hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)
