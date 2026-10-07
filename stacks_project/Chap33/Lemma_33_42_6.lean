module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteComponents

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.42.6: let `X` be a scheme and let `T ⊆ X` be a finite set of points. Assume `X`
has finitely many irreducible components and that, for every irreducible component `Z`, the
inverse image of `T` in the reduced induced closed subscheme on `Z` is contained in an affine
open of that component subscheme. Then there exists an affine open subscheme of `X`
containing `T`. -/
@[stacks 09NM] #check
  (AlgebraicGeometry.Scheme.exists_affineOpen_containing_finiteSet_of_irreducibleComponents :
    ∀ {X : Scheme.{u}} [Finite (irreducibleComponents X)] (T : Set X), T.Finite →
      (∀ Z : irreducibleComponents X,
        let Y := X.irreducibleComponentSubscheme Z
        let i : Y ⟶ X := X.irreducibleComponentSubschemeι Z
        ∃ U : Y.affineOpens, ∀ x : Y, i x ∈ T → x ∈ ((U : Y.Opens) : Set Y)) →
      ∃ U : X.affineOpens, T ⊆ ((U : X.Opens) : Set X))
