/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Module.IdealPower.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Resolutions of ideal-power torsion modules

This file records the source-facing shape of a resolution by direct sums of positive
ideal-power quotients. The canonical epimorphism used at each stage is owned by
`ModuleCat.IdealPower.Cover`.

@stack 05E8
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace ChainComplex.IdealPowerResolution

variable {R : Type u} [CommRing R]

/-- A chain complex is termwise a direct sum of quotients `R ⧸ Iⁿ`, with a positive exponent
that may vary between summands and degrees. -/
@[stacks 05E8 "termwise direct sums of positive ideal-power quotients"]
def IsTermwiseQuotientSum (I : Ideal R) (F : ChainComplex (ModuleCat.{u} R) ℕ) : Prop :=
  ∀ i : ℕ, ∃ (ι : Type u) (exponent : ι → ℕ+),
    Nonempty (F.X i ≃ₗ[R] (⨁ j : ι, R ⧸ I ^ (exponent j : ℕ)))

/-- Lemma 15.89.2: an `I`-power torsion module admits an infinite resolution whose terms are
direct sums of quotients `R ⧸ Iⁿ`, with the positive exponent varying between summands. -/
@[stacks 05E8 "Lemma 15.89.2"]
theorem exists_resolution (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : Module.IsIdealPowerTorsion I M) :
    ∃ (F : ChainComplex (ModuleCat.{u} R) ℕ)
      (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M),
      QuasiIso π ∧ IsTermwiseQuotientSum I F := sorry
-- Proof strategy: iterate the canonical epimorphism `ModuleCat.IdealPower.Cover.π`,
-- taking kernels degree by degree; `kernel_torsion` permits the iteration, while
-- `source_torsion` and the cover description establish the termwise quotient-sum property.

end ChainComplex.IdealPowerResolution
