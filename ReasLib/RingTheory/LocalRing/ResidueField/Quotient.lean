/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.RingHom.Local.Quotient

@[expose] public section

/-!
# Residue fields of local quotients

@stack 05WQ

This leaf relates the residue fields at the closed points of a local ring and
of a proper quotient.  The general comparison between a prime ideal and the
zero ideal of its quotient is owned by
`ReasLib.RingTheory.Ideal.ResidueField.Quotient`; it has no local-ring
hypotheses and is deliberately not re-exported here.
-/

namespace IsLocalRing.ResidueField

universe u

/-- The canonical map on residue fields induced by quotienting a local ring by
a proper ideal is bijective.  The quotient local-ring and local-homomorphism
structures are constructed from the properness witness, so users only need to
provide the mathematical hypothesis `I ≠ ⊤`. -/
@[stacks 05WQ "proper local quotient preserves residue field"]
theorem map_quotient_mk_bijective
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    let _ : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Function.Bijective (IsLocalRing.ResidueField.map (Ideal.Quotient.mk I)) := sorry

/-- A bijective residue-field map remains bijective after passing through
compatible quotients with proper target ideal.  Properness of the source ideal
follows from compatibility, while `IsLocalHom.quotient` installs locality of
the induced quotient map. -/
@[stacks 05WQ "residue-field map of compatible local quotients"]
theorem map_quotientMap_bijective
    {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    {f : R →+* S} [IsLocalHom f] {I : Ideal R} {J : Ideal S}
    (hIJ : I ≤ Ideal.comap f J) (hJ : J ≠ ⊤)
    (hf : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.quotient I (ne_top_of_le_ne_top (Ideal.comap_ne_top f hJ) hIJ)
    let _ : IsLocalRing (S ⧸ J) := IsLocalRing.quotient J hJ
    let _ : IsLocalHom (Ideal.quotientMap J f hIJ) := IsLocalHom.quotient hIJ hJ
    Function.Bijective
      (IsLocalRing.ResidueField.map (Ideal.quotientMap J f hIJ)) := sorry

end IsLocalRing.ResidueField
