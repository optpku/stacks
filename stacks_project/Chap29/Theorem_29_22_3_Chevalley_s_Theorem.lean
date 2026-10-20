/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

/- Theorem 29.22.3 (Chevalley's Theorem): Let `f : X ⟶ Y` be a morphism of schemes. Assume `f` is
quasi-compact and locally of finite presentation. Then the image of every locally constructible
subset is locally constructible. -/
@[stacks 054K] #check
  (AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] [QuasiCompact f] {s : Set X},
      Topology.IsLocallyConstructible s → Topology.IsLocallyConstructible (f '' s))
