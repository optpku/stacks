module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

/-!
# Symmetric monoidal complexes of module sheaves

The reusable construction is the Koszul symmetric structure on cochain complexes. This file
records only its specialization to modules on a ringed space.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/- Lemma 20.50.1: cochain complexes of `𝒪_X`-modules, with the total-complex tensor product,
form a symmetric monoidal category with the Koszul symmetry. -/
@[stacks 0FP8]
#check
  (CochainComplex.Koszul.symmetricCategory (C := Modules X) :
    SymmetricCategory (CochainComplex (Modules X) ℤ))

end AlgebraicGeometry.RingedSpace
