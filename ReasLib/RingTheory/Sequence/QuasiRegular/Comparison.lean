module

public import ReasLib.RingTheory.Sequence.QuasiRegular
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Comparison of Quasi-Regularity Presentations

The canonical predicate `RingTheory.Sequence.IsQuasiRegularSequence` is the
module-valued comparison map specialized to `M = R`. The quotient-Rees map
`RingTheory.Sequence.QuasiRegular.sequenceAssociatedGradedMap` has a different
concrete carrier; this leaf characterizes quasi-regularity through it.
-/

@[expose] public section

universe u

namespace RingTheory.Sequence.IsQuasiRegularSequence

variable {R : Type u} [CommRing R]

/-- A finite sequence is quasi-regular exactly when its quotient-Rees
associated-graded map `(R / I)[X_1, …, X_n] → gr_I(R)` is bijective. -/
@[stacks 061P "quotient-Rees characterization of quasi-regular sequences"]
theorem quotientRees_iff (rs : List R) :
    IsQuasiRegularSequence rs ↔
      Function.Bijective (QuasiRegular.sequenceAssociatedGradedMap rs) := sorry

end RingTheory.Sequence.IsQuasiRegularSequence
