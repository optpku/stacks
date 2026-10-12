/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Filtration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artin–Rees for scheme modules

This file states the global Artin–Rees theorem for a coherent module on a Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- For a coherent module ℱ on a Noetherian scheme, a quasi-coherent subobject 𝒢, and ideal
sheaf data I, there is a uniform c such that
I^(n-c)(I^c ℱ ⊓ 𝒢) = I^n ℱ ⊓ 𝒢 for every n ≥ c. -/
@[stacks 01YA]
theorem exists_artinReesConstant
    [IsNoetherian X]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (𝒢 : Subobject ℱ) [((𝒢 : X.Modules)).IsQuasicoherent]
    (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ n ≥ c,
      idealPowerSmulSubobject I
          ((idealPowerProductSubobject I ℱ c) ⊓ 𝒢) (n - c) =
        idealPowerProductSubobject I ℱ n ⊓ 𝒢 := sorry

end AlgebraicGeometry.Scheme.Modules
