/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open AlgebraicGeometry.SchemeOverField.RationalTail

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.23.2: for a proper one-dimensional scheme over a field with constant global
functions and at-worst-nodal singularities, the curve dualizing module has negative degree
on every rational tail. -/
@[stacks 0E63] #check
  (AlgebraicGeometry.SchemeOverField.dualizingRestrictionDegree_lt_zero_of_rationalTail :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      (h_dimension : topologicalKrullDim X.left = 1) →
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) →
      (h_nodal : atWorstNodal X) →
      let _ : EquidimensionalSpace X.left :=
        equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
      let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
      let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
      ∀ (C : RationalTail X),
        @Scheme.Modules.curveDegreeOfInvertible k _ _
            (componentOver X C.component).hom
            (componentOver_isProper X C.component)
            (componentOver_dimension_eq_one X h_dimension h_global C.component).le
            ((Scheme.Modules.pullback (componentIdeal X C.component).subschemeι).obj
              (Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule X.hom))
            (dualizingRestriction_isInvertible X C.component) < 0)

end AlgebraicGeometry.SchemeOverField
