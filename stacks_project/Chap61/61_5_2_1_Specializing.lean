/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.WLocalHull.Specializing

/-!
# Specializing localizations

The `A`-algebra of points specializing to a standard locally closed stratum
`D(f) ∩ V(I)` is the localization of `A` at the preimage of the units of
`(A ⧸ I)_f`.
-/

@[expose] public section

universe u

#check (Algebra.WLocalHull.stratumSections :
  ∀ (ring : Type u) [CommRing ring], ring → Ideal ring → Type u)

#check (@Localization.toAwayQuotient :
  ∀ (ring : Type u) [CommRing ring] (element : ring) (ideal : Ideal ring),
    ring →+* Algebra.WLocalHull.stratumSections ring element ideal)

#check (@Localization.specializingSubmonoid :
  ∀ (ring : Type u) [CommRing ring], ring → Ideal ring → Submonoid ring)

#check (@Localization.specializing :
  ∀ (ring : Type u) [CommRing ring], ring → Ideal ring → Type u)

#check (@Localization.mem_specializingSubmonoid_iff :
  ∀ (ring : Type u) [CommRing ring] (element : ring) (ideal : Ideal ring)
    {value : ring}, value ∈ Localization.specializingSubmonoid element ideal ↔
      IsUnit (Localization.toAwayQuotient element ideal value))
