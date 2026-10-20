/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Cotangent

/-!
# Relative-cotangent maps along morphisms in `Ĉ_Λ`

Morphisms in `CompleteLocalAlgCat Λ k` induce maps of the relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)`, where `m_Λ` is
`RingHom.ker (algebraMap Λ k)`.
-/

@[expose] public section

open IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.Hom.mapRelative :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : CompleteLocalAlgCat.Hom R S),
    (R.maximalIdeal ⧸ CompleteLocalAlgCat.relativeSubmodule R) →ₗ[Λ]
      (S.maximalIdeal ⧸ CompleteLocalAlgCat.relativeSubmodule S))
