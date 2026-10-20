module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible.Decomposition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

/- Lemma 21.49.2 (1) (0FPY): tensor-invertible derived module sheaves are exactly those with a
locally finite invertible factor decomposition. -/
@[stacks 0FPY "(1)"]
#check @SheafOfModules.RingedSite.isInvertible_iff_hasDecomposition

/- Lemma 21.49.2 (2) (0FPY): every tensor-invertible derived module sheaf is perfect. -/
@[stacks 0FPY "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.of_isInvertible

/- Lemma 21.49.2 (3) (0FPY): on a locally ringed site, tensor-invertibility is equivalent to
being locally a shift of an invertible module. -/
@[stacks 0FPY "(3)"]
#check @SheafOfModules.RingedSite.isInvertible_iff_isLocallyShiftedInvertible

#check @SheafOfModules.RingedSite.InvertibleFamily
#check @SheafOfModules.RingedSite.InvertibleDecomposition
#check @SheafOfModules.RingedSite.HasInvertibleDecomposition
#check @RingedSite.Hom.ModuleDerived.IsLocallyShiftedInvertible
