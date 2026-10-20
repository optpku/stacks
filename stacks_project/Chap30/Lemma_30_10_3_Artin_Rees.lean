/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.ArtinRees
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.10.3 (Artin-Rees): for a Noetherian scheme X, a coherent module ℱ, a
quasi-coherent subobject 𝒢, and ideal-sheaf data I, there is a uniform c such that
I^(n-c)(I^c ℱ ⊓ 𝒢) = I^n ℱ ⊓ 𝒢 for every n ≥ c. -/
@[stacks 01YA] #check (
  AlgebraicGeometry.Scheme.Modules.exists_artinReesConstant :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (𝒢 : Subobject ℱ) [((𝒢 : X.Modules)).IsQuasicoherent]
      (I : X.IdealSheafData),
      ∃ c : ℕ, ∀ n ≥ c,
        AlgebraicGeometry.Scheme.Modules.idealPowerSmulSubobject I
            ((AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject I ℱ c) ⊓ 𝒢)
            (n - c) =
          AlgebraicGeometry.Scheme.Modules.idealPowerProductSubobject I ℱ n ⊓ 𝒢)
