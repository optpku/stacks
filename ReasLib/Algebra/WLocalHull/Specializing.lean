/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Specializing

/-!
# Specializing localizations

The `A`-algebra of points specializing to a standard locally closed stratum
`D(f) ∩ V(I)` is the localization of `A` at the preimage of the units of
`(A ⧸ I)_f`.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- Sections of the structure sheaf on the standard locally closed stratum
`D(f) ∩ V(I)`, realized as the localization `(A ⧸ I)_f`.
This chart interface is used by the closed-stage products and their transition
maps; the specializing localization itself is owned by `Localization.specializing`. -/
abbrev stratumSections (f : A) (I : Ideal A) : Type u :=
  Localization.Away (Ideal.Quotient.mk I f)

end Algebra.WLocalHull
