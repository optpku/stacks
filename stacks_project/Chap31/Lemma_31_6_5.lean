/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FieldExtension
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.6.5: for a field extension `K/k`, a weakly associated point of the base change of a
quasicoherent module maps to a weakly associated point of the original module. -/
@[stacks 0CUC] #check
  (AlgebraicGeometry.Scheme.Modules.FieldExtension.mem_weakAss_of_mem_weakAss :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      y ∈ (Scheme.Modules.FieldExtension.baseChange k K f ℱ).weakAss →
        AlgebraicGeometry.FieldExtension.toSource k K f y ∈ ℱ.weakAss)
