/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.GroupCohomology.ProjectiveLinearBoundary
import StacksCheckRecall

@[expose] public section

universe u v

open scoped MatrixGroups

/- 59.61.5.1: the boundary sends `(σ, τ)` to the scalar represented by
`(lift σ)⁻¹ * lift (σ * τ) * (σ • (lift τ)⁻¹)`. -/
@[stacks 0A2I] #check (brauerTwoCocycle :
  ∀ (K : Type u) {Ksep : Type v} [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : 0 < d)
    (c : Gal(Ksep/K) → PGL(d, Ksep))
    (lift : Gal(Ksep/K) → GL (Fin d) Ksep)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = c σ),
    Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ)

end
