module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.26.3: tensoring a quasi-isomorphism on the right by a K-flat complex preserves
quasi-isomorphisms.  The owner is coefficient-category generic. -/

variable (X : RingedSpace.{u})

@[stacks 06YA "fixed-right K-flat tensoring preserves quasi-isomorphisms"]
#check
  CochainComplex.IsKFlat.quasiIso_tensorHom_left (C := Modules X)

end AlgebraicGeometry.RingedSpace
