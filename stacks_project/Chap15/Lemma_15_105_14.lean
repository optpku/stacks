module

public import ReasLib.RingTheory.Etale.Weakly.Colimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.105.14 (092N)

@stack 092N
-/

/- Lemma 15.105.14 (Stacks `092N`) (1): a localization of a ring is weakly etale. -/
@[stacks 092N "Lemma 15.105.14 (1), localizations are weakly etale"]
#check @Algebra.WeaklyEtale.of_isLocalization

/- Lemma 15.105.14 (Stacks `092N`) (2): every etale ring map is weakly etale. -/
@[stacks 092N "Lemma 15.105.14 (2), etale maps are weakly etale"]
#check @Algebra.WeaklyEtale.of_etale

/- Lemma 15.105.14 (Stacks `092N`) (3): filtered colimits of weakly etale algebras are weakly
etale. -/
@[stacks 092N "Lemma 15.105.14 (3), filtered-colimit closure"]
#check @Algebra.WeaklyEtale.of_isColimit
