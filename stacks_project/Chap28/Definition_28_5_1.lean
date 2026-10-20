/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

variable (X : AlgebraicGeometry.Scheme.{u}) (R : CommRingCat.{u})

/- Definition 28.5.1 (1): a scheme `X` is locally Noetherian via the canonical mathlib predicate
`IsLocallyNoetherian X`, whose affine incarnation is detected by Noetherian coordinate rings. -/
@[stacks 01OV]
#check (AlgebraicGeometry.IsLocallyNoetherian X : Prop)

/- Companion check: for an affine scheme `Spec R`, local Noetherianity is equivalent to the ring
`R` being Noetherian. -/
#check (AlgebraicGeometry.isLocallyNoetherian_Spec (R := R) :
  AlgebraicGeometry.IsLocallyNoetherian (AlgebraicGeometry.Spec R) ↔ IsNoetherianRing R)

/- Definition 28.5.1 (2): a scheme `X` is Noetherian via the canonical mathlib predicate
`IsNoetherian X`; for schemes this is equivalent to being locally Noetherian and quasi-compact,
encoded topologically as `CompactSpace X`. -/
@[stacks 01OV]
#check (AlgebraicGeometry.IsNoetherian X : Prop)

/- Companion check: the canonical scheme-level characterization of Noetherian schemes is local
Noetherianity together with quasi-compactness. -/
#check (AlgebraicGeometry.isNoetherian_iff (X := X) :
  AlgebraicGeometry.IsNoetherian X ↔
    AlgebraicGeometry.IsLocallyNoetherian X ∧ CompactSpace X)
