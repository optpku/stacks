/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.GeometricRegularity.Equiv
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Identity regular ring maps

@stack 07BZ
-/

namespace RingHom.Regular

universe u

/-- The identity homomorphism of a commutative ring is regular. -/
@[stacks 07BZ "identity regular ring map"]
instance instId (R : Type u) [CommRing R] : (RingHom.id R).Regular := sorry

end RingHom.Regular

#synth ∀ (R : Type) [CommRing R], (RingHom.id R).Regular
