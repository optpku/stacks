/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

#check (Algebra.WLocalHull.toStratumSections :
  ∀ (ring : Type u) [CommRing ring] (element : ring) (ideal : Ideal ring),
    ring →+* Algebra.WLocalHull.stratumSections ring element ideal)

#check (Algebra.WLocalHull.specializingSubmonoid :
  ∀ (ring : Type u) [CommRing ring], ring → Ideal ring → Submonoid ring)

#check (Algebra.WLocalHull.specializingLocalization :
  ∀ (ring : Type u) [CommRing ring], ring → Ideal ring → Type u)

#check (Algebra.WLocalHull.specializingSubmonoid_mem_iff :
  ∀ (ring : Type u) [CommRing ring] (element : ring) (ideal : Ideal ring)
    {value : ring}, value ∈ Algebra.WLocalHull.specializingSubmonoid ring element ideal ↔
      IsUnit (Algebra.WLocalHull.toStratumSections ring element ideal value))
