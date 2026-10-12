/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Tricanonical
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.25.3 (1): for a proper one-dimensional scheme over a field with connected
    global functions, genus at least two, at-worst-nodal singularities, and ample dualizing
    sheaf, the third tensor power of the dualizing sheaf is very ample. -/
@[stacks 0E8X] #check (AlgebraicGeometry.SchemeOverField.tricanonicalVeryAmple :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom]
    (h_dimension_one : topologicalKrullDim X.left = 1)
    (h_global :
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension_one h_global)
    (h_at_worst_nodal : atWorstNodal X)
    (h_ample : Scheme.Modules.isAmpleObject (curveDualizingModule X.hom)),
    RelativelyVeryAmple X.hom
      (RingedSpace.TensorPower.sheaf (curveDualizingModule X.hom) 3))

/- Lemma 53.25.3 (2): under the same hypotheses, the first cohomology of the third
    tensor power of the dualizing sheaf vanishes. -/
@[stacks 0E8X] #check (AlgebraicGeometry.SchemeOverField.tricanonicalH1Vanishing :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom]
    (h_dimension_one : topologicalKrullDim X.left = 1)
    (h_global :
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension_one h_global)
    (h_at_worst_nodal : atWorstNodal X)
    (h_ample : Scheme.Modules.isAmpleObject (curveDualizingModule X.hom)),
    IsZero (Scheme.Hom.cohomology X.hom
      (RingedSpace.TensorPower.sheaf (curveDualizingModule X.hom) 3) 1))

end AlgebraicGeometry.SchemeOverField
