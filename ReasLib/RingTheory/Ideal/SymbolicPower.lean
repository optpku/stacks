/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symbolic powers of prime ideals

The `n`th symbolic power of a prime ideal is the contraction of its `n`th
ordinary power from the localization at that prime.  This file owns the
definition together with its quotient-kernel, primary, and radical APIs.

The exponent is allowed to be zero: the zeroth symbolic power is `⊤`.

@stack 0313
@stack 0BC0
-/

@[expose] public section

universe u v

namespace Ideal

open Localization Localization.AtPrime

variable {R : Type u} [CommRing R]
variable (𝔭 : Ideal R) [𝔭.IsPrime]

/-- For a prime ideal `𝔭` of `R`, its `n`th symbolic power is the contraction
of the `n`th power of its extension to `Localization.AtPrime 𝔭`. -/
@[stacks 0313 "symbolic power of a prime ideal"]
def symbolicPower (n : ℕ) : Ideal R :=
  comap (algebraMap R (Localization.AtPrime 𝔭))
    (map (algebraMap R (Localization.AtPrime 𝔭)) 𝔭 ^ n)

/-- The zeroth symbolic power of a prime ideal is the unit ideal. -/
@[simp, stacks 0313 "zeroth symbolic power"]
theorem symbolicPower_zero : symbolicPower 𝔭 0 = ⊤ := sorry
/- Proof strategy: unfold `symbolicPower`, rewrite `pow_zero`, and simplify the
comap of the top ideal. -/

/-- The symbolic power `𝔭.symbolicPower n` is the kernel of the canonical map
from `R` to the quotient of `Localization.AtPrime 𝔭` by the `n`th power of
the extended ideal. -/
@[stacks 0313 "symbolic power as a quotient kernel"]
theorem symbolicPower_eq_ker_quotient_map_pow (n : ℕ) :
    symbolicPower 𝔭 n =
      RingHom.ker
        ((Ideal.Quotient.mk
          (map (algebraMap R (Localization.AtPrime 𝔭)) 𝔭 ^ n)).comp
            (algebraMap R (Localization.AtPrime 𝔭))) := sorry
/- Proof strategy: unfold `symbolicPower`, express both kernels as ideal
comaps, and use `Ideal.mk_ker` for the quotient map. -/

/-- A positive symbolic power of a prime ideal is primary. -/
@[stacks 0313 "positive symbolic powers are primary"]
theorem symbolicPower_isPrimary {n : ℕ} (hn : 0 < n) :
    (symbolicPower 𝔭 n).IsPrimary := sorry
/- Proof strategy: identify the extended prime with the localization's maximal
ideal, show its positive power has maximal radical, and comap the resulting
primary ideal along the localization map. -/

/-- The radical of a positive symbolic power is the original prime ideal. -/
@[stacks 0313 "radical of a positive symbolic power"]
theorem radical_symbolicPower {n : ℕ} (hn : 0 < n) :
    radical (symbolicPower 𝔭 n) = 𝔭 := sorry
/- Proof strategy: commute radical with comap, reduce the positive power to the
localized maximal ideal, and use `Localization.AtPrime.under_maximalIdeal`. -/

section FlatBaseChange

variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Symbolic powers commute with flat extension when the extended prime
remains prime. -/
@[stacks 0BC0]
theorem map_symbolicPower_eq_symbolicPower_map
    (𝔭 : Ideal R) [𝔭.IsPrime] [(map (algebraMap R S) 𝔭).IsPrime] (n : ℕ) :
    map (algebraMap R S) (𝔭.symbolicPower n) =
      (map (algebraMap R S) 𝔭).symbolicPower n := sorry

end FlatBaseChange

end Ideal
