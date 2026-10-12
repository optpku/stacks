/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Appending regular sequences

Regularity of concatenated sequences can be characterized by regularity of a
prefix and of the remaining sequence on the quotient by that prefix.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Regularity of an appended sequence is equivalent to regularity of its
prefix together with regularity of the tail on the quotient by that prefix. -/
theorem append_iff {rs ts : List R} :
    IsRegular M (rs ++ ts) ↔
      IsRegular M rs ∧
        IsRegular (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ts := sorry

/-- A regular sequence remains regular after adjoining a sequence that is
regular on the quotient by its prefix. -/
@[stacks 065K "regular-sequence concatenation"]
theorem append {rs ts : List R} (hrs : IsRegular M rs)
    (hts : IsRegular (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ts) :
    IsRegular M (rs ++ ts) := sorry

/-- After quotienting a module by any prefix of a regular sequence, its
remaining tail is regular.  The quotient is kept as an `R`-module, avoiding
an unnecessary choice of quotient-ring presentation. -/
theorem tail_quotient {rs : List R} (hreg : IsRegular M rs) (i : ℕ) :
    IsRegular (M ⧸ (Ideal.ofList (rs.take i) • (⊤ : Submodule R M))) (rs.drop i) := sorry

end RingTheory.Sequence.IsRegular
