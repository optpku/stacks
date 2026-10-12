/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.FiniteLocallyFree

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/- Lemma 37.68.3: if `Z ⟶ S` is finite locally free and every finite set of
points of `X` over a common point of `S` lies in an affine open of `X`, then
`Mor_S(Z, X)` is representable by a scheme over `S`. -/
@[stacks 0BL4] #check
  (AlgebraicGeometry.Scheme.RelativeHom.representableOfFiniteLocallyFree :
    ∀ {S : Scheme.{u}} (Z X : Over S), [IsFiniteLocallyFree Z.hom] →
      (∀ (s : S) (E : Set X.left), E.Finite →
        (∀ x ∈ E, X.hom x = s) →
        ∃ U : X.left.affineOpens, E ⊆ ((U : X.left.Opens) : Set X.left)) →
      ∃ H : Over S, Nonempty ((functor Z X).RepresentableBy H))

end AlgebraicGeometry.Scheme.RelativeHom
