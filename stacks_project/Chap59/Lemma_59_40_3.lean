/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.RingedTopos
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 59.40.3 -/
@[stacks 04LW] #check
  (AlgebraicGeometry.Scheme.Hom.eq_of_smallEtaleRingedTopos_twoIso :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {a b : X ⟶ Y},
      Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u + 1}
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedHom a).toToposHom
        (AlgebraicGeometry.Scheme.Etale.Small.liftedRingedHom b).toToposHom) →
      a = b)
