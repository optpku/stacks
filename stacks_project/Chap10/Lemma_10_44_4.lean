/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
# Geometric reducedness tests

Lemma 10.44.4 (Tag 030V) is retained as a source-facing recall block.  Its five-way TFAE
packaging is not an appropriate shared owner: the reusable API is split into the finite purely
inseparable criterion, the first Frobenius-root criterion, the perfect-closure criterion, and
mathlib's algebraic-closure characterization.

@stack 030V
-/

/- Lemma 10.44.4 (Tag 030V), finite purely inseparable extensions. -/
@[stacks 030V]
#check @Algebra.IsGeometricallyReduced.FinitePurelyInseparable.iff_forall_isReduced_tensorProduct
#check @Algebra.IsGeometricallyReduced.FinitePurelyInseparable.of_forall_isReduced_tensorProduct

/- Lemma 10.44.4 (Tag 030V), the first Frobenius-root test. -/
@[stacks 030V]
#check @Algebra.IsGeometricallyReduced.OnePthRoot.iff_isReduced_tensorProduct

/- Lemma 10.44.4 (Tag 030V), the relative perfect-closure test. -/
@[stacks 030V]
#check @Algebra.IsGeometricallyReduced.PerfectClosure.iff_isReduced_tensorProduct

/- Lemma 10.44.4 (Tag 030V), the algebraic-closure test from mathlib. -/
@[stacks 030V]
#check @Algebra.isGeometricallyReduced_field_iff
