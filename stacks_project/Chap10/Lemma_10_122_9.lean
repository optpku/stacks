/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.QuasiFinite.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.9

The pointwise locus and spectrally-surjective descent criteria are owned by
`ReasLib.RingTheory.QuasiFinite.BaseChange`; unconditional stability is the
canonical Mathlib ring-hom property.

@stack 00PP
-/

/- Lemma 10.122.9 (1): the quasi-finite locus after base change is the inverse
image of the original quasi-finite locus. -/
@[stacks 00PP "(1), quasi-finite locus under base change"]
#check @Algebra.QuasiFiniteAt.locus_baseChange

#check @Algebra.QuasiFiniteAt.baseChange_iff

/- Lemma 10.122.9 (2): a spectrally surjective base change detects global
quasi-finiteness. -/
@[stacks 00PP "(2), descent along a spectrally surjective base change"]
#check @Algebra.QuasiFinite.iff_baseChange_of_comap_surjective

/- Lemma 10.122.9 (3): every base change of a quasi-finite ring map is
quasi-finite. -/
@[stacks 00PP "(3), stability under arbitrary base change"]
#check @Algebra.FiniteType.QuasiFinite.baseChange

#check @Algebra.FiniteType.baseChange
#check @Algebra.QuasiFinite.baseChange
#check @RingHom.QuasiFinite.isStableUnderBaseChange
