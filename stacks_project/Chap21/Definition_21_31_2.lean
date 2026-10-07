module

public import ReasLib.Topology.Category.LCCat.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemiRepresentableFamily.Over

/- Definition 21.31.2: a fixed-target family in `LCCat` is a qc covering when every target
point has a neighborhood contained in finitely many images of compact source subsets. -/
@[stacks 09X0]
#check @IsQuasiCompactCovering

/- The indexed family in the source is the `ofArrows` presentation of the bundled owner. -/
@[stacks 09X0 "indexed presentation"]
#check @IsQuasiCompactCovering.ofArrows_iff

/- A useful open-neighborhood form of the defining condition. -/
#check @IsQuasiCompactCovering.exists_open_subset_compact_image
