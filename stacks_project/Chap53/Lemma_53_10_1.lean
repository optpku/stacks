module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.GenusZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.10.1: an invertible module of degree zero on a proper genus-zero curve whose
global functions are exactly the ground field is isomorphic to the structure module. -/
@[stacks 0C6M]
#check
  (AlgebraicGeometry.SchemeOverField.isoUnit_of_genus_zero_of_degree_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom],
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
      Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0 →
      (L : X.left.Modules) → [Scheme.Modules.Invertible L] →
      Scheme.Modules.curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le L = 0 →
      Nonempty (L ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))

end AlgebraicGeometry.SchemeOverField
