/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 56.6.2 -/
@[stacks 0GPF] #check
  (AlgebraicGeometry.Scheme.QCoh.exists_nonzero_hom_of_moduleSupport_subset :
    ∀ {X : Scheme.{u}} [IsAffine X] (F E : Scheme.QCoh X)
      [F.obj.IsFinitePresentation], ¬ IsZero E →
      Scheme.Modules.moduleSupport E.obj ⊆ Scheme.Modules.moduleSupport F.obj →
      ∃ f : F ⟶ E, f ≠ 0)
