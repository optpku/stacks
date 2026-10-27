/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.RingHom.SquareZero

@[expose] public section

/-!
# Closed points of square-zero extensions

A square-zero extension of a local ring has a canonical closed point on its
target, obtained by mapping the source maximal ideal.  Working with this ideal
directly avoids installing a theorem-produced local-ring instance merely to
form the induced map on residue fields.

-/

universe u v w

namespace RingHom.IsSquareZeroExtension

/-- The target of a square-zero extension from a local ring is nontrivial. -/
theorem targetNontrivial {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    [IsLocalRing A'] (π : A' →+* A) [π.IsSquareZeroExtension] :
    Nontrivial A := sorry

/-- The closed point on the target of a square-zero extension from a local
ring. -/
abbrev targetMaximalIdeal {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    [IsLocalRing A'] (π : A' →+* A) [π.IsSquareZeroExtension] : Ideal A :=
  Ideal.map π (IsLocalRing.maximalIdeal A')

/-- The target closed point of a square-zero extension is maximal. -/
instance targetMaximalIdeal_isMaximal {A' : Type u} {A : Type v}
    [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) [π.IsSquareZeroExtension] :
    (targetMaximalIdeal π).IsMaximal := sorry

/-- The canonical target prime carried by a square-zero extension from a local
ring.  It packages the induced maximal ideal without installing a
theorem-produced `IsLocalRing` instance on the target.
-/
def targetClosedPoint {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    [IsLocalRing A'] (π : A' →+* A) [π.IsSquareZeroExtension] : PrimeSpectrum A :=
  ⟨targetMaximalIdeal π, inferInstance⟩

/-- The underlying ideal of the canonical target prime is the induced target
maximal ideal.
-/
@[simp]
theorem targetClosedPoint_asIdeal {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    [IsLocalRing A'] (π : A' →+* A) [π.IsSquareZeroExtension] :
    (targetClosedPoint π).asIdeal = targetMaximalIdeal π := sorry

/-- When the target is already equipped with its local-ring structure, the
canonical extension point is the usual local closed point.
-/
theorem targetClosedPoint_eq_closedPoint {A' : Type u} {A : Type v}
    [CommRing A'] [CommRing A] [IsLocalRing A'] [IsLocalRing A]
    (π : A' →+* A) [π.IsSquareZeroExtension] :
    targetClosedPoint π = IsLocalRing.closedPoint A := sorry

/-- Pulling the target closed point back along the extension recovers the
source maximal ideal. -/
@[simp]
theorem comap_targetMaximalIdeal {A' : Type u} {A : Type v}
    [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) [π.IsSquareZeroExtension] :
    (targetMaximalIdeal π).comap π = IsLocalRing.maximalIdeal A' := sorry

/-- A map from a local ring to the target of a square-zero extension carries
the closed point to the target closed point. -/
def IsLocalAtClosedPoint {A' : Type u} {A : Type v} {S : Type w}
    [CommRing A'] [CommRing A] [CommRing S] [IsLocalRing A'] [IsLocalRing S]
    (π : A' →+* A) [π.IsSquareZeroExtension] (g : S →+* A) : Prop :=
  IsLocalRing.maximalIdeal S = (targetMaximalIdeal π).comap g

/-- The map on residue fields induced by a map carrying the source closed
point to the target closed point of a square-zero extension. -/
noncomputable abbrev residueFieldMap
    {A' : Type u} {A : Type v} {S : Type w}
    [CommRing A'] [CommRing A] [CommRing S] [IsLocalRing A'] [IsLocalRing S]
    (π : A' →+* A) [π.IsSquareZeroExtension] (g : S →+* A)
    (hg : IsLocalAtClosedPoint π g) :
    (IsLocalRing.maximalIdeal S).ResidueField →+*
      (targetMaximalIdeal π).ResidueField :=
  Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) (targetMaximalIdeal π) g hg

end RingHom.IsSquareZeroExtension
