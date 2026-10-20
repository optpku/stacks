/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.RingedTopos
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 59.40.2 -/
@[stacks 04IJ] #check
  (AlgebraicGeometry.Scheme.Hom.smallEtale_twoMorphism_eq_id :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      (t : RingedSite.ToposHom.TwoMorphism.{u + 1, u, u + 1, u, u + 1}
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedHom f).toToposHom
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedHom f).toToposHom),
      t = RingedSite.ToposHom.TwoMorphism.refl.{u + 1, u, u + 1, u, u + 1} _)
