module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.Topology.Sober.GenericPoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) {Z : Set X}
variable (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)

/- Lemma 26.11.1: an irreducible closed subset of a scheme has a unique generic point. -/
@[stacks 01IS] #check hZ.existsUnique_isGenericPoint hZclosed

#synth QuasiSober X
#synth T0Space X
