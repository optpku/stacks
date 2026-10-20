/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Affine.RingedTopos
public import stacks_project.Chap35.Lemma_35_8_7_AssociatedModule

/-!
# Affine comparisons for the small Zariski and étale ringed topoi

This source-facing module selects the canonical affine comparison for either
of the two standard small sites.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology

/-- The canonical affine-to-small morphism of ringed topoi for the selected
Zariski or étale topology. -/
noncomputable def affineComparison (τ : SmallStandardTopology) (S : Scheme.{u}) :
    match τ with
    | .zariski => RingedSite.ToposHom
        (Scheme.Zariski.SmallAffineComparison.affineRingedSite S)
        (Scheme.Zariski.Small.liftedRingedSite S)
    | .etale => RingedSite.ToposHom
        (Scheme.Etale.SmallAffineComparison.affineRingedSite S)
        (Scheme.Etale.Small.liftedRingedSite S) :=
  match τ with
  | .zariski => Scheme.Zariski.SmallAffineComparison.comparison S
  | .etale => Scheme.Etale.SmallAffineComparison.comparison S

end AlgebraicGeometry.SmallStandardTopology
