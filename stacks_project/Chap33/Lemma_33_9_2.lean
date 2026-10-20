module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral.Decomposition
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/- Lemma 33.9.2: a scheme over a field is geometrically integral if and only if
it is both geometrically reduced and geometrically irreducible. -/
@[stacks 038K]
#check (AlgebraicGeometry.SchemeOverField.GeometricallyIntegral.iff_geometricallyReduced_and_geometricallyIrreducible X :
  AlgebraicGeometry.GeometricallyIntegral X.hom ↔
    AlgebraicGeometry.GeometricallyReduced X.hom ∧
      AlgebraicGeometry.GeometricallyIrreducible X.hom)
