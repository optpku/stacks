module

public import Mathlib.Algebra.MvPolynomial.Basic
public import ReasLib.RingTheory.Sequence.Regularity
import StacksCheckRecall

/-!
# A regular sequence whose reordering is not regular

@stack 00LG
-/

@[expose] public section

universe u

open MvPolynomial RingTheory.Sequence

variable (k : Type u) [CommRing k] [Nontrivial k]

/-- **Example 10.68.2** ([Stacks tag 00LG](https://stacks.math.columbia.edu/tag/00LG)):
in `k[x, y, z]`, the sequence `x, y(1 - x), z(1 - x)` is regular, whereas the
reordered sequence `y(1 - x), z(1 - x), x` is not. -/
@[stacks 00LG]
theorem example10682_regularSequence_and_reordered_not_regular :
    IsRegular (MvPolynomial (Fin 3) k)
        [(X 0 : MvPolynomial (Fin 3) k),
          X 1 * (1 - X 0),
          X 2 * (1 - X 0)] ∧
      ¬ IsRegular (MvPolynomial (Fin 3) k)
        [X 1 * (1 - X 0),
          X 2 * (1 - X 0),
          (X 0 : MvPolynomial (Fin 3) k)] := sorry

@[stacks 00LG "canonical regular-sequence predicate"]
#check @RingTheory.Sequence.IsRegular

@[stacks 00LG "inductive regular-sequence criterion"]
#check @RingTheory.Sequence.isRegular_cons_iff
