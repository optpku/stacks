module

public import ReasLib.RingTheory.Localization.StandardOpenCover
import StacksCheckRecall

@[expose] public section

open PrimeSpectrum

/- Definition 26.5.2 (1): a standard open cover of an affine spectrum is a finite family of
principal opens covering the whole spectrum. -/
@[stacks 01HT] #check StandardOpenCover

/- Definition 26.5.2 (2): more generally, a standard open cover of `D(f)` is a finite family of
principal opens whose supremum is `D(f)`. -/
@[stacks 01HT] #check StandardOpenCoverOf

#check StandardOpenCoverOf.ofGenerator
#check StandardOpenCoverOf.spec
#check StandardOpenCoverOf.exists_refinement_of_open_cover
#check StandardOpenCoverOf.restrictionRingHom
#check StandardOpenCoverOf.restrictionModuleMap
