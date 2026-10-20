/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Cohomology
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 30.3.4: let `f : X ⟶ Y` be a quasi-compact morphism with `X` and `Y`
quasi-separated. If `R¹ f_* I = 0` for every quasi-coherent ideal sheaf `I` on `X`, then `f`
is affine. -/
@[stacks 0F83] #check
  (AlgebraicGeometry.Scheme.isAffineHom_of_R1_pushforward_vanishes_for_quasiCoherent_idealSheaves :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
      [QuasiSeparatedSpace X.carrier] [QuasiSeparatedSpace Y.carrier]
      [HasInjectiveResolutions X.Modules],
      (∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj I.toModule)) →
      IsAffineHom f)
