/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.IdealPower.TorsionIdeal
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

/-!
# Kollár's exceptional finite-extension alternative

This leaf owns the reusable predicates behind the fourth alternative in
Kollár's local-ring dichotomy.  The existential owner is separated from the
explicit ring-hom view, and the chapter-facing names remain thin bridges in
the source file.
-/

@[expose] public section

universe u

namespace IsLocalRing.Kollar

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Kollár's exceptional alternative: a nontrivial finite `R`-algebra whose canonical map is not
bijective, whose kernel and cokernel are killed by one power of the maximal ideal, and for which
the maximal ideal is not an associated prime of the target. -/
@[stacks 0BHZ "Kollár exceptional finite extension"]
def HasExceptionalExtension : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ : Nontrivial S),
    ¬ Function.Bijective (algebraMap R S) ∧
      (∃ n : ℕ,
        (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
        (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
      maximalIdeal R ∉ associatedPrimes R S

/-- The defining finite-algebra package for `HasExceptionalExtension R`. -/
@[stacks 0BHZ "Kollár exceptional extension specification"]
theorem hasExceptionalExtension_iff :
    HasExceptionalExtension R ↔
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S)
        (_ : Nontrivial S),
        ¬ Function.Bijective (algebraMap R S) ∧
          (∃ n : ℕ,
            (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S := sorry

/-- A destructuring view of a Kollár exceptional extension witness. -/
@[stacks 0BHZ "Kollár exceptional extension witness specification"]
theorem HasExceptionalExtension.spec (h : HasExceptionalExtension R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S)
      (_ : Nontrivial S),
      ¬ Function.Bijective (algebraMap R S) ∧
        (∃ n : ℕ,
          (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
          (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
        maximalIdeal R ∉ associatedPrimes R S := sorry

/-- The canonical maximal-ideal power-torsion ideal used in Kollár's construction. -/
@[stacks 0BHZ "maximal-ideal power-torsion ideal"]
abbrev powerTorsionIdeal : Ideal R :=
  Ideal.powerTorsionIdeal (maximalIdeal R)

namespace powerTorsionIdeal

/-- Membership in the local power-torsion ideal is annihilation by a power of the maximal ideal. -/
@[simp, stacks 0BHZ "local maximal-ideal power-torsion membership"]
theorem mem_iff (x : R) :
    x ∈ powerTorsionIdeal R ↔
      ∃ n : ℕ, (maximalIdeal R) ^ n ≤ Ideal.torsionOf R R x := sorry

/-- In a Noetherian local ring, one power of the maximal ideal annihilates the whole
power-torsion ideal. -/
@[stacks 0BHZ "uniform maximal-ideal power-torsion bound"]
theorem exists_pow_smul_eq_bot [IsNoetherianRing R] :
    ∃ n : ℕ, (maximalIdeal R) ^ n • powerTorsionIdeal R = ⊥ := sorry

/-- If the local power-torsion ideal vanishes, the maximal ideal is not an associated prime of the
self-module. -/
@[stacks 0BHZ "self-module associated-prime exclusion"]
theorem maximalIdeal_not_mem_associatedPrimes_self_of_eq_bot
    (hJzero : powerTorsionIdeal R = ⊥) :
    maximalIdeal R ∉ associatedPrimes R R := sorry

/-- Quotienting a Noetherian local ring by its maximal-ideal power-torsion ideal removes the
maximal ideal from the associated primes. -/
@[stacks 0BHZ "power-torsion quotient associated-prime exclusion"]
theorem maximalIdeal_not_mem_associatedPrimes_quotient [IsNoetherianRing R] :
    maximalIdeal R ∉ associatedPrimes R (R ⧸ powerTorsionIdeal R) := sorry

end powerTorsionIdeal

end IsLocalRing.Kollar

namespace RingHom.Kollar

variable {R : Type u} {S : Type u} [CommRing R] [IsLocalRing R] [CommRing S]

/-- A ring map is a Kollár exceptional extension when its induced algebra satisfies the finite,
non-bijective, maximal-ideal-power torsion, and associated-prime conditions. -/
@[stacks 0BHZ "map-level Kollár exceptional extension"]
def IsExceptionalExtension (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Nontrivial S ∧
    Module.Finite R S ∧
      ¬ Function.Bijective f ∧
        (∃ n : ℕ,
          (IsLocalRing.maximalIdeal R) ^ n • (RingHom.ker f : Submodule R R) = ⊥ ∧
            (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤
              (Algebra.linearMap R S).range) ∧
          IsLocalRing.maximalIdeal R ∉ associatedPrimes R S

namespace IsExceptionalExtension

/-- The explicit conjunction underlying `RingHom.Kollar.IsExceptionalExtension f`. -/
@[stacks 0BHZ "map-level exceptional-extension specification"]
theorem spec (f : R →+* S) :
    IsExceptionalExtension f ↔
      let _ : Algebra R S := f.toAlgebra
      Nontrivial S ∧
        Module.Finite R S ∧
          ¬ Function.Bijective f ∧
            (∃ n : ℕ,
              (IsLocalRing.maximalIdeal R) ^ n • (RingHom.ker f : Submodule R R) = ⊥ ∧
                (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤
                  (Algebra.linearMap R S).range) ∧
              IsLocalRing.maximalIdeal R ∉ associatedPrimes R S := sorry

/-- A map-level witness yields the existential Kollár exceptional-extension owner. -/
@[stacks 0BHZ "map-to-owner exceptional-extension bridge"]
theorem has (f : R →+* S) (hf : IsExceptionalExtension f) :
    IsLocalRing.Kollar.HasExceptionalExtension R := sorry

end IsExceptionalExtension

end RingHom.Kollar
