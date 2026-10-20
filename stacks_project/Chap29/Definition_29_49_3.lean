/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.AffineSpace
import StacksCheckRecall

@[expose] public section

-- A rational function is stated directly as Mathlib's `RationalMap` to the
-- canonical affine line, so no item-specific mathematical owner is needed.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/- Source/core/bridge triage:
- `source-facing`: Definition 29.49.3 identifies the notion of a rational function on a scheme `X`;
- `core/canonical`: mathlib already owns rational maps as `Scheme.RationalMap`, written `X ⤏ Y`;
- `bridge/view`: the source target is mathlib's canonical universe-polymorphic affine line over
  `Spec ℤ`.

This item is therefore a pure canonical identification: a rational function on `X` is simply a rational
map from `X` to the integral affine line. No extra local owner or alias is needed.
-/

universe u

variable (X : Scheme.{u})

/- Definition 29.49.3: a rational function on `X` is a rational map from `X` to the affine line
over `ℤ`, represented by the canonical universe-polymorphic affine-space object. -/
@[stacks 01RT] #check
  (AlgebraicGeometry.Scheme.RationalMap X
    (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of (ULift.{u} ℤ)))) : Type u)

end AlgebraicGeometry.Scheme
