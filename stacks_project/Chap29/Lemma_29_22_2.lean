/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.22.2: Let `f : X ⟶ Y` be a quasi-compact morphism of schemes that is locally of
finite presentation. If `Y` is quasi-compact and quasi-separated, then the image of every
constructible subset of `X` is constructible in `Y`. -/
@[stacks 054J] #check
  (AlgebraicGeometry.Scheme.Hom.isConstructible_image :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
      [CompactSpace Y] [QuasiSeparatedSpace Y] {s : Set X},
      Topology.IsConstructible s → Topology.IsConstructible (f '' s))
