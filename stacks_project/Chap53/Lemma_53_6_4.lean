/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.Vanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

namespace ProperDualizingComplex

/- Lemma 53.6.4: in Situation 53.6.2, if `L` is a globally generated invertible
module that is not isomorphic to the structure module, then
`H¹(X, curveDualizingModule X.hom ⊗ L) = 0`. -/
@[stacks 0B62] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.firstCohomology_tensor_isZero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      topologicalKrullDim X.left = 1 →
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
      ∀ (L : X.left.Modules) [Scheme.Modules.Invertible L]
        [SheafOfModules.IsGloballyGenerated L],
        ¬ RingedSpace.IsTrivial L →
        IsZero (Scheme.Hom.cohomology X.hom
          (curveDualizingModule X.hom ⊗ L) 1))

end ProperDualizingComplex

end AlgebraicGeometry.Scheme.DerivedQCoh
