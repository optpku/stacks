/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.Pow
public import ReasLib.RingTheory.Ideal.Derivation.Pow
public import ReasLib.RingTheory.Kaehler.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler base change along successive ideal-power quotients

This leaf owns the canonical comparison between Kähler differentials before
and after replacing `S` by `S ⧸ I ^ (n + 1)`, then base changing to
`S ⧸ I ^ n`.

@stack 02HQ
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

universe u v

namespace KaehlerDifferential.Quotient.Pow

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

section

variable (I : Ideal S) (n : ℕ)

local notation "Sₙ" => S ⧸ I ^ n
local notation "Sₙ₊₁" => S ⧸ I ^ (n + 1)

/-- The canonical Kähler base-change map from `S` to the quotient by
`I ^ (n + 1)`, after both sides are base changed to `S ⧸ I ^ n`. -/
@[stacks 02HQ "successive ideal-power Kähler base change"]
noncomputable def baseChange :
    Sₙ ⊗[S] Ω[S⁄R] →ₗ[Sₙ] Sₙ ⊗[Sₙ₊₁] Ω[Sₙ₊₁⁄R] :=
  BaseChange.map (R := R) (I ^ (n + 1)) (I ^ n)
    (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The differential of `I ^ (n + 1)` vanishes modulo `I ^ n`; this is the
Leibniz-rule input for the successive-power quotient comparison.  Its
elementwise algebraic core is
`Derivation.mem_smul_top_of_mem_pow_succ`. -/
@[stacks 02HQ "successive ideal-power differential vanishing"]
theorem differentialVanishesMod :
    BaseChange.differentialVanishesMod (R := R) (I ^ (n + 1)) (I ^ n) := sorry

/-- Lemma 10.131.11, tag `02HQ`: the successive ideal-power Kähler
base-change map is bijective.  This formulation also covers `n = 0`, where
both sides are canonically zero; the source assumption `1 ≤ n` is therefore
not needed by the formal statement. -/
@[stacks 02HQ "successive ideal-power Kähler base change"]
theorem baseChange_bijective :
    Function.Bijective
      ((baseChange (R := R) I n) :
        Sₙ ⊗[S] Ω[S⁄R] →ₗ[Sₙ] Sₙ ⊗[Sₙ₊₁] Ω[Sₙ₊₁⁄R]) := sorry

end

end KaehlerDifferential.Quotient.Pow
