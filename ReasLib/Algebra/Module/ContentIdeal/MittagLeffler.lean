module

public import ReasLib.Algebra.Module.ContentIdeal
public import ReasLib.RingTheory.Flatness.MittagLeffler.SupportingSubmodule
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Content ideals in flat Mittag-Leffler modules

@stack 0ASD
-/

open scoped TensorProduct

universe u v

namespace Module.MittagLeffler

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- Lemma 15.24.4, tag `0ASD`: every element of a flat Mittag-Leffler module
has a content ideal. -/
@[stacks 0ASD "existence of content ideals in flat Mittag-Leffler modules"]
theorem exists_contentIdeal [Module.Flat A M] [MittagLeffler A M] (x : M) :
    ∃ I : Ideal A, IsContentIdeal x I := sorry
-- Proof strategy: apply `exists_least_tensorSupport` to `(TensorProduct.lid A M).symm x` with
-- the finite free module `A`, identify submodules of `A` with ideals, and use
-- `Ideal.subtype_rTensor_range` to rewrite the least-support condition as `IsContentIdeal x I`.

/-- A flat Mittag-Leffler module element has a unique content ideal. -/
@[stacks 0ASD "unique content ideals in flat Mittag-Leffler modules"]
theorem existsUnique_contentIdeal [Module.Flat A M] [MittagLeffler A M]
    (x : M) : ∃! I : Ideal A, IsContentIdeal x I := sorry
-- Proof strategy: combine `exists_contentIdeal x` with `IsContentIdeal.unique`.

end Module.MittagLeffler
