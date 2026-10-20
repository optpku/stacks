/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField

@[expose] public section

/-!
# Pointed etale extensions

@stack 00UL

An `EtalePoint p` is an etale extension equipped with a selected prime over
`p`.  Unlike an `EtaleNeighborhood p`, it does not require the induced map on
residue fields to be bijective.  This distinction is needed when an etale
extension is used to enlarge the residue field before a geometric
decomposition.
-/

universe u v

namespace PrimeSpectrum

/-- A pointed etale extension of a prime `p`, without a residue-field
identification. -/
@[stacks 00UL "pointed etale extension"]
structure EtalePoint {R : Type u} [CommRing R] (p : PrimeSpectrum R) where
  /-- The bundled commutative algebra underlying the etale extension. -/
  toCommAlgCat : CommAlgCat.{v} R
  /-- The extension is etale over the base ring. -/
  etale : Algebra.Etale R toCommAlgCat
  /-- The selected point of the extension. -/
  point : PrimeSpectrum toCommAlgCat
  /-- The selected point lies over `p`. -/
  over : p.asIdeal = Ideal.comap (algebraMap R toCommAlgCat) point.asIdeal

namespace EtalePoint

/-- The underlying type of a pointed etale extension. -/
abbrev carrier {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtalePoint.{u, v} p) : Type v := U.toCommAlgCat

/-- Bundle an etale algebra and a selected point over `p` as an `EtalePoint`. -/
@[stacks 00UL "pointed etale extension constructor"]
def of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal) : EtalePoint p where
  toCommAlgCat := CommAlgCat.of R S
  etale := inferInstance
  point := q
  over := hq

/-- The selected point maps to the base point on prime spectra. -/
@[stacks 00UL "point of a pointed etale extension"]
theorem comap_point {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtalePoint.{u, v} p) :
    PrimeSpectrum.comap (algebraMap R U.carrier) U.point = p := sorry

/-- The etale and lying-over conditions carried by a pointed etale
extension. -/
@[stacks 00UL "pointed etale extension specification"]
theorem spec {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtalePoint.{u, v} p) :
    Algebra.Etale R U.carrier ∧
      PrimeSpectrum.comap (algebraMap R U.carrier) U.point = p := sorry

/-- The canonical residue-field map of a pointed etale extension. -/
@[stacks 00UL "residue field map of a pointed etale extension"]
noncomputable def residueFieldMap {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtalePoint.{u, v} p) :
    p.asIdeal.ResidueField →+* U.point.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal U.point.asIdeal
    (algebraMap R U.carrier) U.over

/-- The non-global algebra structure induced by the residue-field map of a
pointed etale extension. -/
@[stacks 00UL "residue field algebra of a pointed etale extension", implicit_reducible]
noncomputable def residueFieldAlgebra {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtalePoint.{u, v} p) :
    Algebra p.asIdeal.ResidueField U.point.asIdeal.ResidueField :=
  U.residueFieldMap.toAlgebra

end EtalePoint

end PrimeSpectrum
