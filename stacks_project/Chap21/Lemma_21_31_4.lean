module

public import ReasLib.Topology.Category.LCCat.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemiRepresentableFamily.Over

/- The singleton qc-covering criterion used by Lemma 21.31.4. -/
#check @IsQuasiCompactCovering.singleton_iff

/- Lemma 21.31.4: a proper surjective morphism in `LCCat` gives a singleton qc covering. -/
@[stacks 09X5]
#check @IsQuasiCompactCovering.singleton_of_proper_surjective
