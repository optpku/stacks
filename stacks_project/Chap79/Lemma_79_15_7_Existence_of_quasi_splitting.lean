/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Definition_79_15_1_Splitting
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_ResiduePoint
public import stacks_project.Chap79.Lemma_79_15_7_Existence_of_quasi_splitting_ResiduePoint
public import stacks_project.Chap79.Situation_79_15_4_Quasi_splitting_Setup

/-!
# Existence of a quasi-splitting after étale localization

In Situation 79.15.4 the finite-part localization of a groupoid scheme is
quasi-split over the residue-field point classifying `(u, Z_u)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.7 (Existence of quasi-splitting): in Situation 79.15.4 there exists
an algebraic space `U'`, an étale morphism `U' ⟶ U`, and a point
`u' : Spec (κ(u)) ⟶ U'` lying over `u : Spec (κ(u)) ⟶ U` such that the restriction
`R'` of `R` to `U'` is quasi-split over `u'`. The space `U'` is
`(finitePart (ofScheme G)).U.left`, the étale map is `finitePartToU`, the point
`u'` is `quasiSplittingHom`, and `R'` is the restriction along
`(finitePartHom (ofScheme G)).obj`. -/
@[stacks 04RW]
theorem isQuasiSplitOver_finitePart {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    GroupoidAlgebraicSpace.IsQuasiSplitOver
      (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
        (GroupoidAlgebraicSpace.finitePartHom
          (GroupoidAlgebraicSpace.ofScheme G)).obj)
      (quasiSplittingResiduePoint G u) :=
  sorry

/-- There exist an algebraic space `U'`, an étale morphism `U' ⟶ U`, and a
`Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of `R` is
quasi-split. -/
theorem exists_etale_isQuasiSplitOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G g))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
