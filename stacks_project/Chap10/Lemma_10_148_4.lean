/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Unramified.Locus
import StacksCheckRecall

/-!
@stack 04E8

# Formal Unramifiedness at Prime Localizations

Lemma 10.148.4 is the source-facing TFAE assembled from the canonical
pairwise localization criteria in `ReasLib.RingTheory.Unramified.Locus`.
-/

@[expose] public section

/- Lemma 10.148.4: formal unramifiedness is equivalent to its two prime-local
forms. -/
@[stacks 04E8 "prime-local TFAE"]
#check @Algebra.formallyUnramified_localization_tfae

/- Named pairwise owners for downstream rewriting. -/
@[stacks 04E8 "local-ring-hom criterion at a prime"]
#check @Algebra.isUnramifiedAt_iff_localRingHomAt_formallyUnramified

@[stacks 04E8 "all-primes local-ring-hom criterion"]
#check @Algebra.formallyUnramified_iff_forall_localRingHomAt

#print axioms Algebra.formallyUnramified_localization_tfae
