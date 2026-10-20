module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Module
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.10: for a module sheaf concentrated in degree zero, the first two
pseudo-coherence bounds are finite type and finite presentation. -/

@[stacks 09V9 "(1)"]
#check @SheafOfModules.IsMPseudoCoherent.zero_iff_isFiniteType

@[stacks 09V9 "(2)"]
#check @SheafOfModules.IsMPseudoCoherent.minusOne_iff_isFinitePresentation

-- Directional glue replaces the old proof-dependent pseudo-instances.
#check @SheafOfModules.IsMPseudoCoherent.isFiniteType
#check @SheafOfModules.IsMPseudoCoherent.of_isFiniteType
#check @SheafOfModules.IsMPseudoCoherent.isFinitePresentation
#check @SheafOfModules.IsMPseudoCoherent.of_isFinitePresentation

