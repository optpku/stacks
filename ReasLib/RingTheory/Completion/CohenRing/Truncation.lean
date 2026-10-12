/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import ReasLib.RingTheory.Completion.CohenRing
public import ReasLib.RingTheory.Smooth.Quotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Truncated Cohen rings

This leaf records the characteristic and formal-smoothness API for quotients
of a Cohen ring by positive powers of its residue characteristic.

@stack 0329
-/

universe u

open IsLocalRing

namespace IsCohenRing

variable {Λ : Type u} [CommRing Λ] [IsCohenRing Λ]

local notation "p" => ringChar (ResidueField Λ)

/-- The quotient of a Cohen ring by the `n`-th power of its residue characteristic has
characteristic `p ^ n`. -/
@[stacks 0329 "characteristic of a truncated Cohen ring"]
theorem quotient_span_residueChar_pow_charP (n : ℕ+) :
    CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) := sorry

/-- The characteristic theorem transported to an ideal explicitly identified with the canonical
residue-characteristic-power ideal. -/
@[stacks 0329 "named-ideal characteristic view of a truncated Cohen ring"]
theorem quotient_charP_of_eq
    (n : ℕ+) (I : Ideal Λ)
    (hI : I = Ideal.span {((p ^ (n : ℕ)) : Λ)}) :
    CharP (Λ ⧸ I) (p ^ (n : ℕ)) := sorry

/-- Lemma 10.160.7: a positive residue-characteristic-power quotient of a Cohen ring is formally
smooth over the corresponding `ZMod` algebra. -/
@[stacks 0329 "formal smoothness of a truncated Cohen ring"]
theorem zmodPow_quotient_formallySmooth
    (n : ℕ+) :
    letI : CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) :=
      quotient_span_residueChar_pow_charP n
    letI : Algebra (ZMod (p ^ (n : ℕ)))
        (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) := ZMod.algebra _ _
    Algebra.FormallySmooth (ZMod (p ^ (n : ℕ)))
      (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) := sorry

/-- The canonical algebra map into a positive residue-characteristic-power quotient of a Cohen
ring is formally smooth. -/
@[stacks 0329 "formally smooth map into a truncated Cohen ring"]
theorem zmodPow_quotient_algebraMap_formallySmooth
    (n : ℕ+) :
    letI : CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) :=
      quotient_span_residueChar_pow_charP n
    letI : Algebra (ZMod (p ^ (n : ℕ)))
        (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) := ZMod.algebra _ _
    RingHom.FormallySmooth
      (algebraMap (ZMod (p ^ (n : ℕ)))
        (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)})) := sorry

/-- The ring-hom formal-smoothness theorem transported to an explicitly named copy of the
residue-characteristic-power ideal. -/
@[stacks 0329 "named-ideal formally smooth map into a truncated Cohen ring"]
theorem zmodPow_quotient_algebraMap_formallySmooth_of_eq
    (n : ℕ+) (I : Ideal Λ)
    (hI : I = Ideal.span {((p ^ (n : ℕ)) : Λ)})
    [CharP (Λ ⧸ I) (p ^ (n : ℕ))]
    [Algebra (ZMod (p ^ (n : ℕ))) (Λ ⧸ I)] :
    RingHom.FormallySmooth (algebraMap (ZMod (p ^ (n : ℕ))) (Λ ⧸ I)) := sorry

/-- A natural-number-indexed named-ideal view for consumers that already carry the truncation
exponent as a `Nat` rather than as a positive subtype. -/
@[stacks 0329 "natural-index named-ideal formally smooth map"]
theorem zmodPow_quotient_algebraMap_formallySmooth_of_eq_nat
    (m : ℕ) (I : Ideal Λ)
    (hI : I = Ideal.span {((p ^ m) : Λ)})
    [CharP (Λ ⧸ I) (p ^ m)]
    [Algebra (ZMod (p ^ m)) (Λ ⧸ I)] :
    RingHom.FormallySmooth (algebraMap (ZMod (p ^ m)) (Λ ⧸ I)) := sorry

end IsCohenRing
