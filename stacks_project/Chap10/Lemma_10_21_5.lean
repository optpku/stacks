module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.21.5

@stack 00EH
-/

/- Lemma 10.21.5 (1).  `IsIdempotentElem I` is the source equation `I = I ^ 2`, and the
owner returns the required idempotent principal generator. -/
@[stacks 00EH "(1), finitely generated idempotent ideal"]
#check @Ideal.isIdempotentElem_iff_of_fg

/- Lemma 10.21.5 (2).  Apply the owner to the complementary idempotent `1 - e`; its quotient
ideal `span {1 - (1 - e)}` is the source ideal `R ∙ e`. -/
@[stacks 00EH "(2), idempotent quotient as an away localization"]
#check @IsLocalization.Away.quotient_of_isIdempotentElem

/- Lemma 10.21.5 (3).  Rewriting `R ∙ e` as `span {e}` gives the source zero-locus formula. -/
@[stacks 00EH "(3), idempotent zero locus"]
#check @PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem
