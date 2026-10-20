/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.DimensionOne
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.6.1: a proper one-dimensional scheme over a field whose canonical map from the
field to its global sections is bijective is connected, Cohen–Macaulay, and equidimensional. -/
@[stacks 0BY5]
#check (@AlgebraicGeometry.SchemeOverField.connectedSpace_of_dim_one_of_globalSectionsMap_bijective :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      topologicalKrullDim X.left = 1 →
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) → ConnectedSpace X.left)

#check (@AlgebraicGeometry.SchemeOverField.cohenMacaulay_of_dim_one_of_globalSectionsMap_bijective :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      topologicalKrullDim X.left = 1 →
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) → Scheme.CohenMacaulay X.left)

#check (@AlgebraicGeometry.SchemeOverField.equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      topologicalKrullDim X.left = 1 →
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
          TopologicalSpace.EquidimensionalSpace X.left)

end AlgebraicGeometry.SchemeOverField
