/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Pullback
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 29.25.14: If `f : Y ⟶ X` is flat and `ℱ` is a finite-type quasicoherent
`X.Modules` object with scheme-theoretic support `I`, then `I.comap f` is the
scheme-theoretic support of `(Scheme.Modules.pullback f).obj ℱ`. -/
@[stacks 07T9] #check
  (IsSchemeTheoreticSupport.pullback_of_flat :
    ∀ {X Y : Scheme.{u}} (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (I : X.IdealSheafData), IsSchemeTheoreticSupport ℱ I →
        ∀ (f : Y ⟶ X) [Flat f],
          IsSchemeTheoreticSupport ((Scheme.Modules.pullback f).obj ℱ) (I.comap f))

end AlgebraicGeometry.Scheme.Modules
