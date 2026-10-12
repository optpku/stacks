/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular Sequences in Short Exact Sequences

@stack 0F1T

This leaf records the extension property for regular sequences in a short
exact sequence of modules.
-/

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

open RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable {rs : List R}

/-- Lemma 10.68.8 (0F1T): if a sequence is regular on both end terms of a short exact sequence,
then it is regular on the middle term. -/
@[stacks 0F1T "regular sequences are stable under extensions"]
theorem isRegular_X₂ (hS : S.ShortExact) (hX₁ : IsRegular S.X₁ rs)
    (hX₃ : IsRegular S.X₃ rs) : IsRegular S.X₂ rs := sorry

end CategoryTheory.ShortComplex.ShortExact
