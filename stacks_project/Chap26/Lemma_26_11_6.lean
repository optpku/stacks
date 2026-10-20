module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardOpen
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

/- Lemma 26.11.6: an affine open has a finite standard-open cover refining a chosen affine-open
cover of the ambient scheme. -/
@[stacks 01IX] #check AffineOpenCover.exists_standardRefinement
#check AffineOpenCover.StandardRefinement
#check AffineOpenCover.StandardRefinement.iSup_affineOpen_eq
#check AffineOpenCover.StandardRefinement.spec
#check AffineOpenCover.StandardRefinement.affineOpen_le_opensRange
#check StandardZariskiCover.OnAffineOpen.iSup_eq

end AlgebraicGeometry.Scheme
