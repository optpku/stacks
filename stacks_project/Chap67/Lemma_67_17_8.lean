/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X Y U : AlgebraicSpace S}
variable [OverClass X B] [OverClass Y B] [Separated (Y ↘ B)]
variable {ι : U ⟶ X} [IsOpenImmersion ι] [IsSchemeTheoreticallyDominant ι]

/- Lemma 67.17.8: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `f, g : X ⟶ Y` be morphisms of algebraic spaces over `B`. Let `U ⊆ X` be
an open subspace such that `f|_U = g|_U`. If the scheme theoretic closure of
`U` in `X` is `X` and `Y ⟶ B` is separated, then `f = g`. -/
@[stacks 084N] #check
  (AlgebraicGeometry.AlgebraicSpace.ext_of_schemeTheoreticClosure_of_isSeparated
    (S := S) (B := B) (X := X)
    (Y := Y) (U := U) ι :
      ∀ {f g : X ⟶ Y} [HomIsOver f B] [HomIsOver g B],
        ι ≫ f = ι ≫ g → f = g)

end AlgebraicGeometry.AlgebraicSpace
