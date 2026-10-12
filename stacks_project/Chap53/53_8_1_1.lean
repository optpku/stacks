/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Genus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- 53.8.1.1: for a proper one-dimensional scheme `X` over `k` whose global
functions are `k`, its genus `g = dim_k H¹(X, 𝒪_X)` is also
`dim_k H⁰(X, ω_X)`. -/
@[stacks 0BY8] #check (AlgebraicGeometry.SchemeOverField.genus_eq_dualizingModule_finrank :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
    genus X h_dimension hΓ = Scheme.Hom.cohomologyFinrank X.hom
      (curveDualizingModule X.hom) 0)

end AlgebraicGeometry.SchemeOverField
