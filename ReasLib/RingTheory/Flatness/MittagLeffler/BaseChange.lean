/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat
public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct

/-!
# Base change of Mittag-Leffler modules

The Mittag-Leffler property is stable under extension of scalars.  Unlike restriction of scalars,
the source ring is part of the tensor-product type, so the canonical closure fact is registered as
an instance.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.MittagLeffler

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Lemma 10.94.1 (2), tag `05A3`: extension of scalars preserves the Mittag-Leffler property. -/
@[stacks 05A3 "(2)"]
instance baseChange [MittagLeffler R M] : MittagLeffler S (S ⊗[R] M) := sorry

/-- Explicit-hypothesis form of `Module.MittagLeffler.baseChange`. -/
theorem baseChange_of (hM : MittagLeffler R M) : MittagLeffler S (S ⊗[R] M) := sorry

namespace BaseChange

/-- A universally injective algebra map reflects the Mittag-Leffler property after extension of
scalars. -/
@[stacks 05A5 "universally injective reflection"]
theorem of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S))
    (hM : MittagLeffler S (S ⊗[R] M)) : MittagLeffler R M := sorry

/-- Extension of scalars along a universally injective algebra map preserves and reflects the
Mittag-Leffler property. -/
@[stacks 05A5 "universally injective base change"]
theorem iff_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    MittagLeffler R M ↔ MittagLeffler S (S ⊗[R] M) := sorry

end BaseChange

/-- Lemma 10.95.1, tag `05A5`: the Mittag-Leffler property descends along a faithfully flat
extension. -/
@[stacks 05A5]
theorem of_baseChange [Module.FaithfullyFlat R S]
    (hM : MittagLeffler S (S ⊗[R] M)) : MittagLeffler R M := sorry

/-- Faithfully flat base change preserves and reflects the Mittag-Leffler property. -/
@[stacks 05A5 "faithfully flat base change iff"]
theorem iff_baseChange [Module.FaithfullyFlat R S] :
    MittagLeffler R M ↔ MittagLeffler S (S ⊗[R] M) := sorry

end Module.MittagLeffler
