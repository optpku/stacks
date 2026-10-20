module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.SchemeLocalization

/-!
# Affine étale scheme localization with a quasi-splitting

A groupoid scheme satisfying the quasi-splitting hypotheses, with affine object
scheme and flat, locally finitely presented source and target, admits an
affine étale scheme localization quasi-split at a point with the same residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme satisfying the quasi-splitting hypotheses at a point, with
affine object scheme and flat, locally finitely presented source and target,
admits an affine étale scheme localization with a point above the given point
inducing an isomorphism on residue fields, at which the restricted groupoid
is quasi-split. -/
theorem exists_affineEtale_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- A groupoid scheme satisfying the quasi-splitting hypotheses at a point, with
affine object scheme and flat, locally finitely presented source and target,
admits an affine étale scheme localization with a point valued in the original
residue field, factoring the canonical residue map, at which the restricted
groupoid is quasi-split. The commuting equation and étaleness ensure that the
point induces an isomorphism on residue fields. -/
theorem exists_affineEtale_residueMap_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
