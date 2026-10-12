/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Comparison of Quasi-Regularity Presentations

The quotient-Rees presentation of ring-valued quasi-regularity and the
module-valued associated-graded comparison map have different concrete
carriers. This leaf records their common ring-level predicate without making
one model a definitional alias for the other.
-/

@[expose] public section

universe u

namespace RingTheory.Sequence.IsQuasiRegularSequence

variable {R : Type u} [CommRing R]

/-- The module-valued quasi-regularity predicate specialized to `R` agrees
with the quotient-Rees presentation of a finite sequence. -/
theorem quotientRees_iff (rs : List R) :
    RingTheory.Sequence.IsQuasiRegularSequence rs ↔
      RingTheory.Sequence.QuasiRegular.IsQuasiRegularSequence rs := sorry

end RingTheory.Sequence.IsQuasiRegularSequence
