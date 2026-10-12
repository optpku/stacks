/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.SquareZero.Shift
import StacksCheckRecall

/-!
# A nonsplit universally injective map of free modules

Example 15.15.5 is recalled from the explicit square-zero shift owner. The owner also exposes the
cokernel and each property in the source's side remark.

@stack 05GR
-/

@[expose] public section

@[stacks 05GR "Example 15.15.5, coefficient ring"]
#check @MvPolynomial.SquareZero.Shift.Ring

@[stacks 05GR "Example 15.15.5, shift map"]
#check @MvPolynomial.SquareZero.Shift.map

@[stacks 05GR "Example 15.15.5 (1), auto-associated ring"]
#check @MvPolynomial.SquareZero.Shift.ring_isAutoAssociated

@[stacks 05GR "Example 15.15.5 (2), injective"]
#check @MvPolynomial.SquareZero.Shift.injective

@[stacks 05GR "Example 15.15.5 (3), universally injective"]
#check @MvPolynomial.SquareZero.Shift.universallyInjective

@[stacks 05GR "Example 15.15.5 (4), residue map bijective"]
#check @MvPolynomial.SquareZero.Shift.quotientMapByMaximalIdeal_bijective

@[stacks 05GR "Example 15.15.5 (5), not surjective"]
#check @MvPolynomial.SquareZero.Shift.not_surjective

@[stacks 05GR "Example 15.15.5 (6), not split"]
#check @MvPolynomial.SquareZero.Shift.not_split

@[stacks 05GR "Example 15.15.5, cokernel"]
#check @MvPolynomial.SquareZero.Shift.Cokernel

@[stacks 05GR "Example 15.15.5 (7), flat cokernel"]
#check @MvPolynomial.SquareZero.Shift.cokernel_flat

@[stacks 05GR "Example 15.15.5 (8), countably generated cokernel"]
#check @MvPolynomial.SquareZero.Shift.cokernel_countablyGenerated

@[stacks 05GR "Example 15.15.5 (9), nonprojective cokernel"]
#check @MvPolynomial.SquareZero.Shift.cokernel_not_projective

@[stacks 05GR "Example 15.15.5 (10), non-Mittag-Leffler cokernel"]
#check @MvPolynomial.SquareZero.Shift.cokernel_not_mittagLeffler
