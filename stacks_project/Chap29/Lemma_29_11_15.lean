/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.11.15: let `j : Y ⟶ X` be an immersion of schemes. If there is an open
`U ⊆ X` whose inclusion and the restriction of `j` are affine, and if the part of the image of
`j` over the complement of `U` is closed, then `j` is affine. -/
@[stacks 0C3A] #check
  (AlgebraicGeometry.isAffineHom_of_exists_affine_restrict_and_closed_compl :
    ∀ {X Y : Scheme.{u}} (j : Y ⟶ X), [IsImmersion j] →
      (∃ U : X.Opens,
        IsAffineHom U.ι ∧ IsAffineHom (j ∣_ U) ∧
          IsClosed (Set.range j ∩ (U : Set X)ᶜ)) →
        IsAffineHom j)

/- Under the same hypotheses, an affine target gives an affine source. -/
#check
  (AlgebraicGeometry.isAffine_of_exists_affine_restrict_and_closed_compl :
    ∀ {X Y : Scheme.{u}} (j : Y ⟶ X), [IsImmersion j] → [IsAffine X] →
      (∃ U : X.Opens,
        IsAffineHom U.ι ∧ IsAffineHom (j ∣_ U) ∧
          IsClosed (Set.range j ∩ (U : Set X)ᶜ)) →
        IsAffine Y)
