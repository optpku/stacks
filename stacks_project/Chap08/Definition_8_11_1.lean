module

public import ReasLib.CategoryTheory.Fibered.Gerbe.FiberClasses
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.11.1 — Bridge

Definition 8.11.1 defines gerbes over a site. The canonical owner is now
`CategoryTheory.IsGerbe` in `CategoryTheory/Fibered/Gerbe/Basic.lean`.
-/

namespace CategoryTheory

@[stacks 06NZ]
#check @IsGerbe

#check @IsGerbe.locallyInhabited
#check @IsGerbe.locallyIsomorphic
#check @IsGerbe.iff_coverwise
#check @IsGerbe.of_coverwise
#check @IsGerbe.FiberClasses.iff
#check @IsGerbe.fiberClassesLocallySurjective
#check @IsGerbe.fiberClassesLocallyInjective

end CategoryTheory
