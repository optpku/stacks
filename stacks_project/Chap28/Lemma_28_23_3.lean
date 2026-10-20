/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.23.3: every quasi-coherent module on a scheme is the directed colimit of its
quasi-coherent `κ`-generated submodules for a cardinal `κ` depending only on the scheme. -/
@[stacks 077N] #check
  (AlgebraicGeometry.Scheme.Modules.exists_cardinal_kappaGeneratedQuasiCoherentSubobjects_isDirectedColimit :
    ∀ X : Scheme.{u}, ∃ κ : Cardinal.{u}, ∀ ℱ : X.Modules,
      ℱ.IsQuasicoherent →
        DirectedOn (· ≤ ·)
            (AlgebraicGeometry.Scheme.Modules.kappaGeneratedQuasiCoherentSubobjects κ ℱ) ∧
          IsLUB
            (AlgebraicGeometry.Scheme.Modules.kappaGeneratedQuasiCoherentSubobjects κ ℱ)
            (⊤ : Subobject ℱ))
