/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine.RingedTopos

/-!
# Ringed-topos comparison for affine standard sites

This compatibility module re-exports the canonical affine-to-big ringed-topos
comparison.
-/

@[expose] public section

universe u

/- The canonical comparison has the expected affine-to-big direction. -/
#check (AlgebraicGeometry.StandardTopology.Affine.comparison :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
    RingedSite.ToposHom
      (AlgebraicGeometry.StandardTopology.Affine.ringedSite τ S)
      (AlgebraicGeometry.StandardTopology.Big.liftedRingedSite τ S))
