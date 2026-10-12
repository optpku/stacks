/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Polynomial.NilpotenceLocus
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.29.8 (Tag 00FC): fiberwise nilpotence is detected by characteristic coefficients.

@stack 00FC
-/

@[stacks 00FC "fiberwise nilpotence locus"]
#check @Algebra.nilpotenceLocus

@[stacks 00FC "characteristic-polynomial equations"]
#check @Algebra.NilpotenceLocus.eq_zeroLocus_charpoly_coeffs

@[stacks 00FC "pointwise characteristic-polynomial equations"]
#check @Algebra.NilpotenceLocus.mem_iff_forall_charpoly_coeff_mem

@[stacks 00FC "source fiber nilpotence criterion"]
#check @Algebra.NilpotenceLocus.isNilpotent_iff_mem_zeroLocus

@[stacks 00FC "closed fiberwise nilpotence locus"]
#check @Algebra.NilpotenceLocus.isClosed
