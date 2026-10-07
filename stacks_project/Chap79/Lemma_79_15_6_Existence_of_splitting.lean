module

public import stacks_project.Chap79.Definition_79_15_1_Splitting
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_ResiduePoint
public import stacks_project.Chap79.Lemma_79_15_6_Existence_of_splitting_ResiduePoint
public import stacks_project.Chap79.Situation_79_15_3_Splitting

/-!
# Existence of a splitting after étale localization

In Situation 79.15.3 the finite-part localization of a groupoid scheme is
split over the residue-field point classifying `(u, Z_u)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.6 (Existence of splitting): in Situation 79.15.3 there exists
an algebraic space `U'`, an étale morphism `U' ⟶ U`, and a point
`u' : Spec (κ(u)) ⟶ U'` lying over `u : Spec (κ(u)) ⟶ U` such that the restriction
`R'` of `R` to `U'` is split over `u'`. The space `U'` is
`(finitePart (ofScheme G)).U.left`, the étale map is `finitePartToU`, the point
`u'` is `splittingHom`, and `R'` is the restriction along
`(finitePartHom (ofScheme G)).obj`. -/
@[stacks 0DTC]
theorem isSplitOver_finitePart {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    GroupoidAlgebraicSpace.IsSplitOver
      (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
        (GroupoidAlgebraicSpace.finitePartHom
          (GroupoidAlgebraicSpace.ofScheme G)).obj)
      (splittingResiduePoint G u) :=
  sorry

/-- There exist an algebraic space `U'`, an étale morphism `U' ⟶ U`, and a
`Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of `R` is
split. -/
theorem exists_etale_isSplitOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G g))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
