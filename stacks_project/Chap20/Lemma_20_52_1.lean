module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.52.1 (0FPF): global sections induce an equivalence from finite-free-retract
module sheaves to finite projective modules over the global-sections ring. -/
@[stacks 0FPF]
#check @AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective.globalSections_isEquivalence

-- The equivalence, its two functors, and the objectwise global-sections result are reusable
-- independently of the typeclass-facing statement.
#check @AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective.equivalence
#check @AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective.globalSections
#check @AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective.associated
#check @AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective.globalSections_obj_mem
