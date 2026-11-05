/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties

/-!
# Singleton systems of parameters

This leaf records the one-element bridges between the cotangent-space criterion, partial regular
systems of parameters. For singleton parameter ideals, use
`IsLocalRing.parameterIdeal_fin1_eq_span_singleton`.
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- In a regular local ring, an element outside `𝔪 ^ 2` is a one-element partial regular system
of parameters. -/
theorem isPartOfRegularSystemOfParameters_singleton
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (x : maximalIdeal R)
    (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank
      (fun _ : Fin 1 ↦ x) := sorry

end IsLocalRing
