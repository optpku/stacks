module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.ResiduePoint

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The finite-part localization is quasi-split over the residue-field point
classifying the identity-support open. -/
theorem isQuasiSplitOver_finitePart {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
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
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
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
