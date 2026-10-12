/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.ShortComplex
import StacksCheckRecall

@[expose] public section

/- Lemma 12.5.16 (1) [08N6]: the componentwise kernel row is represented canonically by the
kernel in the abelian category of short complexes. -/
@[stacks 08N6]
#check @CategoryTheory.ShortComplex.kernel_exact_of_exact_of_mono

/- Lemma 12.5.16 (2) [08N6]: dually, the componentwise cokernel row is the canonical cokernel in
the abelian category of short complexes. -/
#check @CategoryTheory.ShortComplex.cokernel_exact_of_exact_of_epi

end
