module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.FilteredColimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.20

@stack 090N
-/

/- Lemma 10.39.20 (Stacks tag `090N`): faithfully flatness of a filtered
colimit of commutative algebras is owned by the fixed-base shared API. -/
@[stacks 090N]
#check @RingHom.FaithfullyFlat.of_isColimit_under

#check @RingHom.FaithfullyFlat.of_colimit_under
