module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Splitting.ResiduePoint

/-!
# Étale localization with a splitting

A groupoid scheme satisfying the splitting hypotheses at an object point
admits an étale algebraic-space localization split over a residue-field point
above that object point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The restriction along the finite-part localization is split over the
residue-field point classifying the stabilizer-support finite part. -/
theorem isSplitOver_finitePart {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)]
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
    (u : G.U.left) [Fact (SplittingHypotheses G u)] :
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
