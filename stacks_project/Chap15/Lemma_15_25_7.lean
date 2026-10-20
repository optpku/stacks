module

public import ReasLib.Algebra.Module.FinitePresentation.ValuationRing
import StacksCheckRecall

/-!
# Lemma 15.25.7

@stack 0GSE

The local essentially-finite-type valuation-ring criteria are owned by the reusable
finite-presentation API.  Both clauses retain the source assumption that `A → B` is local.
-/

@[expose] public section

/- Lemma 15.25.7 (1): a flat local algebra essentially of finite type over a valuation ring is
essentially of finite presentation. -/
@[stacks 0GSE "Lemma 15.25.7 (1)"]
#check @Algebra.EssFinitePresentation.ofFlatEssFiniteTypeLocalValuationRing

/- Lemma 15.25.7 (2): a finite module over a local algebra essentially of finite type over a
valuation ring is finitely presented when it is flat over the valuation ring. -/
@[stacks 0GSE "Lemma 15.25.7 (2)"]
#check @Module.FinitePresentation.ofFiniteFlatEssFiniteTypeLocalValuationRing
