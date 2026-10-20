module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.ResiduePoint

/-! # Strong splitting after étale localization -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The restriction to the finite-part localization is strongly split at the point
classifying the finite open of loop arrows in the residue source fibre. -/
theorem isStronglySplitOver_finitePart {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    GroupoidAlgebraicSpace.IsStronglySplitOver
      (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
        (GroupoidAlgebraicSpace.finitePartHom
          (GroupoidAlgebraicSpace.ofScheme G)).obj)
      (strongSplittingResiduePoint G u) :=
  sorry

/-- There exist an algebraic space `U'`, an étale morphism `U' ⟶ U`, and a
`Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of `R` to
that `U'` is strongly split over that same point. -/
theorem exists_etale_isStronglySplitOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G g))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
