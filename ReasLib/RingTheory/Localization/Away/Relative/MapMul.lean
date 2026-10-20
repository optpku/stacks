/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.Relative

/-!
# Relative maps to product localizations

This leaf names the ring map from `R_r` to `S_{f(r)s}` obtained by first
localizing a ring map `f : R →+* S` and then localizing once more in the
target.  The corresponding non-global algebra action is owned by
`Localization.Away.Relative.mapMulAlgebra`.
-/

@[expose] public section

universe u v

namespace Localization.Away.Relative

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S]

/-- The canonical relative map `R_r → S_{f(r)s}`. -/
@[stacks 051T "relative principal-localization product map",
  stacks 077H "077H away-product support map"]
noncomputable def mapMul (f : R →+* S) (r : R) (s : S) :
    Localization.Away r →+* Localization.Away (f r * s) :=
  (IsLocalization.Away.awayToAwayRight (f r) s).comp
    (Localization.awayMap f r)

end Localization.Away.Relative
