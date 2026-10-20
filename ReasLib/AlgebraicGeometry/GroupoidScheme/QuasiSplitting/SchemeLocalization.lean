/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.EtaleLocalization

/-!
# Separated étale scheme localization with a quasi-splitting

A groupoid scheme satisfying the quasi-splitting hypotheses, with flat and
locally finitely presented source and target, admits a separated étale scheme
localization quasi-split at a point with the same residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme satisfying the quasi-splitting hypotheses at a point,
whose source and target are flat and locally of finite presentation, admits a
separated étale scheme localization with a point above the given point
inducing an isomorphism on residue fields, at which the restricted groupoid
is quasi-split. -/
theorem exists_separatedEtale_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.IsSeparated g.left ∧
        AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
          IsIso (g.left.residueFieldMap u') ∧
            GroupoidAlgebraicSpace.IsQuasiSplitOver
              (GroupoidAlgebraicSpace.pullback
                (GroupoidAlgebraicSpace.ofScheme G)
                (objectRestrictionHom G (ofOverMap g)))
              (ofOver.pointsEquiv U' u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
