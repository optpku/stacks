module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
/- Lemma 17.21.1 (01CG): the degree-`n` exterior and symmetric powers of a module sheaf are
the sheafifications of their sectionwise power presheaves. -/
@[stacks 01CG]
#check @RingedSpace.ExteriorPower.sheaf_eq_sheafification

#check @RingedSpace.SymmetricPower.sheaf_eq_sheafification
