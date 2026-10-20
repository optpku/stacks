/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Unramified Morphisms over Locally Noetherian Schemes

Over a locally Noetherian base, unramified and G-unramified morphisms coincide.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Over a locally Noetherian base, a morphism is unramified if and only if it is
G-unramified. -/
@[stacks 04EV]
theorem Unramified.iff_gUnramified (f : X ⟶ S) [IsLocallyNoetherian S] :
    Unramified f ↔ GUnramified f := by
  constructor
  · intro hf
    exact
      { toFormallyUnramified := hf.toFormallyUnramified
        toLocallyOfFinitePresentation :=
          LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hf.toLocallyOfFiniteType }
  · intro hf
    exact
      { toFormallyUnramified := hf.toFormallyUnramified
        toLocallyOfFiniteType :=
          LocallyOfFinitePresentation.iff_locallyOfFiniteType.mp
            hf.toLocallyOfFinitePresentation }

namespace LocallyOfFiniteType

/-- A locally finite type morphism to a locally Noetherian scheme is unramified if and only if
it is formally unramified. -/
@[stacks 024R]
theorem unramified_iff_formallyUnramified (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    Unramified f ↔ FormallyUnramified f := sorry

end LocallyOfFiniteType

end AlgebraicGeometry
