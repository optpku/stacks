module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

/- Definition 20.26.2: K-flatness for complexes of `𝒪_X`-modules is the specialization of the
coefficient-category predicate `CochainComplex.IsKFlat`; no ringed-space wrapper is needed. -/

variable (X : RingedSpace.{u})

@[stacks 06Y9 "K-flat complexes of modules on a ringed space"]
#check
  (CochainComplex.IsKFlat : CochainComplex (Modules X) ℤ → Prop)

#check @CochainComplex.isKFlat_iff

end AlgebraicGeometry.RingedSpace
