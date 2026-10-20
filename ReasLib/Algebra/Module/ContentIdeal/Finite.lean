module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Algebra.Module.ContentIdeal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finiteness of content ideals

@stack 0ASB
-/

universe u v

namespace IsContentIdeal

variable {A : Type u} {M : Type v}
variable [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- Lemma 15.24.2, tag `0ASB`: every content ideal is finitely generated.

Flatness is unnecessary once the least ideal is supplied, so this statement is
more general than the source context. -/
@[stacks 0ASB "content ideals are finitely generated"]
theorem fg {x : M} {I : Ideal A} (hI : IsContentIdeal x I) : I.FG := sorry
-- Proof strategy: expand `hI.mem` with `Submodule.mem_ideal_smul_span_iff_exists_sum`; the
-- finitely many coefficients span an ideal `J ≤ I` still containing `x`, and `hI.le` gives
-- `I ≤ J`.

end IsContentIdeal
