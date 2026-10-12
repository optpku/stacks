/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Genus
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

/- 55.11.9.1: The genus of the proper geometrically integral component C_{i, k̄}
is at least the genus of its normalization. Here X represents C_{i, k̄} over
the algebraically closed field k̄, and genus means the first structure-sheaf
cohomology dimension. -/
@[stacks 0CEB] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.structureSheafH1Finrank_le :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [IsProper X.hom],
      Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
          (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
            (SchemeOverField.normalization X).left.Modules) 1 ≤
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

end AlgebraicGeometry.SchemeOverField.Normalization
