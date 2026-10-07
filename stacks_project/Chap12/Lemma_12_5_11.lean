module

public import ReasLib.CategoryTheory.Abelian.CommSq
import StacksCheckRecall

@[expose] public section

/- Lemma 12.5.11 (1) [08N2]: pullback squares are characterized by exactness of the canonical
biproduct sequence. -/
@[stacks 08N2]
#check @CategoryTheory.isPullback_iff_exact_biproduct_sequence

/- Lemma 12.5.11 (2) [08N2]: pushout squares satisfy the dual exactness characterization. -/
#check @CategoryTheory.isPushout_iff_exact_biproduct_sequence

end
