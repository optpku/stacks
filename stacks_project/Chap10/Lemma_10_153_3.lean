module

public import ReasLib.RingTheory.Henselian.Criteria
import StacksCheckRecall

@[expose] public section

/-!
# Criteria for henselian local rings

Lemma 10.153.3 is a canonical recall.  Its root/factorization, etale,
finite-product, finite-type, and quasi-finite clauses have independent
reusable owners in `ReasLib.RingTheory.Henselian.Criteria`; product and fiber
data are owned separately rather than repackaged in this source file.

The criterion is formulated at the base universe, since a `Prop` cannot bind
an arbitrary Lean universe level.  The source-universe-polymorphic outcome
theorems in the shared owner provide the corresponding downstream operations.

@stack 04GG
-/

/- Lemma 10.153.3 [stacks 04GG]: henselianity of a local ring is equivalent
to the simple-root, coprime-factorization, etale-neighborhood, finite-algebra,
finite-type, and quasi-finite criteria collected by the reusable owner below.
The original textbook packaging is therefore a recall of the canonical
`List.TFAE`, not a second chapter-local implementation. -/
@[stacks 04GG]
#check @HenselianLocalRing.Criteria.tfae

#check @HenselianLocalRing.Criteria.Root.henselian_iff_simpleLift
#check @HenselianLocalRing.Criteria.Etale.henselian_iff_hasUniqueRetraction
#check @HenselianLocalRing.Criteria.Finite.henselian_iff_finiteLocalProduct
#check @HenselianLocalRing.Criteria.FiniteType.existsNonQuasiFiniteSplit_of_henselian
#check @HenselianLocalRing.Criteria.QuasiFinite.existsZeroFiberSplit_of_henselian
