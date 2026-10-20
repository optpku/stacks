module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting.SchemeLocalization

/-! # Strong splitting after an affine étale scheme localization -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme satisfying the strong-splitting hypotheses at a point,
with affine object scheme and flat, locally finitely presented source and target,
admits an affine étale scheme localization with a point above the given point
inducing an isomorphism on residue fields, at which the canonical restricted
groupoid is strongly split. -/
theorem exists_affineEtale_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- A groupoid scheme satisfying the strong-splitting hypotheses at a point,
with affine object scheme and flat, locally finitely presented source and target,
admits an affine étale scheme localization and a morphism from the residue field
at which the canonical restricted groupoid is strongly split. The commuting
equation with the canonical residue morphism, together with étaleness, ensures
preservation of the residue field. -/
theorem exists_affineEtale_residueMap_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
