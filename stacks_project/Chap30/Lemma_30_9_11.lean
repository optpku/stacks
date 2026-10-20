/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 30.9.11: if a coherent module on an open subscheme is supported on a closed subset
contained in that open, then its pushforward along the open inclusion is coherent. -/
@[stacks 0CYJ] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_of_support_subset :
    ∀ {X : Scheme.{u}} (U : X.Opens) (T : Closeds X)
      (hT : (T : Set X) ⊆ (U : Set X)) (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent],
      AlgebraicGeometry.RingedSpace.moduleSupportedOn
          (Subtype.val ⁻¹' (T : Set X)) ℱ →
        ((AlgebraicGeometry.Scheme.Modules.pushforward U.ι).obj ℱ).IsCoherent)
