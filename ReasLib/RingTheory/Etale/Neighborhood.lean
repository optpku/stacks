/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Category
public import ReasLib.RingTheory.Etale.Point
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField

@[expose] public section

/-!
# Etale neighborhoods of prime ideals

An etale neighborhood bundles the etale algebra, its selected point over the
base point, and the requirement that the induced residue-field map is an
isomorphism.  The selected point need not be closed; maximality is derived
when the base point is maximal.  Keeping the point in the data prevents later
approximation maps from silently switching branches of the etale algebra.
The canonical bridge `EtaleNeighborhood.toEtalePoint` forgets only the
residue-field condition; `EtaleNeighborhood.ofEtalePoint` supplies it again.
@stack 07QZ
-/

universe u v

namespace PrimeSpectrum

/-- An etale neighborhood of a prime consists of an etale algebra with a
selected point lying over the given prime and inducing the same residue field. -/
@[stacks 07QZ "etale neighborhood of a prime"]
structure EtaleNeighborhood {R : Type u} [CommRing R] (p : PrimeSpectrum R) where
  /-- The bundled etale algebra underlying the neighborhood. -/
  etaleAlgebra : CommAlgCat.Etale.{v} R
  /-- The selected point of the etale algebra. -/
  point : PrimeSpectrum etaleAlgebra
  /-- The selected point lies over the base point. -/
  over : p.asIdeal = Ideal.comap (algebraMap R etaleAlgebra) point.asIdeal
  /-- The selected point has the same residue field as the base point. -/
  residueField_bijective : Function.Bijective
    (Ideal.ResidueField.map p.asIdeal point.asIdeal (algebraMap R etaleAlgebra) over)

namespace EtaleNeighborhood

/-- Forget the residue-field condition, preserving the algebra, selected
point, and lying-over proof. -/
def toEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) : EtalePoint.{u, v} p where
  toCommAlgCat := U.etaleAlgebra.obj
  etale := U.etaleAlgebra.property
  point := U.point
  over := U.over

/-- The carrier type of an etale neighborhood. -/
abbrev carrier {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) : Type v := U.etaleAlgebra

/-- The forgetful bridge preserves the carrier. -/
@[simp]
theorem carrier_toEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) : U.toEtalePoint.carrier = U.carrier := rfl

/-- The forgetful bridge preserves the selected point. -/
@[simp]
theorem point_toEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) : U.toEtalePoint.point = U.point := rfl

/-- A pointed etale extension with a bijective canonical residue-field map
is an etale neighborhood. -/
def ofEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtalePoint.{u, v} p) (hres : Function.Bijective U.residueFieldMap) :
    EtaleNeighborhood.{u, v} p where
  etaleAlgebra := { obj := U.toCommAlgCat, property := U.etale }
  point := U.point
  over := U.over
  residueField_bijective := hres

/-- Forgetting an added residue-field condition recovers the supplied point. -/
@[simp]
theorem toEtalePoint_ofEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtalePoint.{u, v} p) (hres : Function.Bijective U.residueFieldMap) :
    (ofEtalePoint U hres).toEtalePoint = U := rfl

/-- Restoring a neighborhood's residue-field condition recovers that neighborhood. -/
@[simp]
theorem ofEtalePoint_toEtalePoint {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    ofEtalePoint U.toEtalePoint U.residueField_bijective = U := rfl

/-- Bundle an etale algebra, a selected point over `p`, and the induced
residue-field identification as an etale neighborhood. -/
@[stacks 07QZ "etale neighborhood constructor"]
def of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal)
    (hres : Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hq)) :
    EtaleNeighborhood p :=
  ofEtalePoint (EtalePoint.of q hq) hres

/-- The neighborhood constructor uses the canonical pointed extension. -/
@[simp]
theorem toEtalePoint_of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal)
    (hres : Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hq)) :
    (of q hq hres).toEtalePoint = EtalePoint.of q hq := rfl

/-- Bundle an etale algebra at the contracted point of a target prime whose
canonical residue-field map is bijective. -/
@[stacks 07QZ "etale neighborhood at a contracted point"]
def ofBijectiveAt {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hres : RingHom.ResidueField.IsBijectiveAt (algebraMap R S) q) :
    EtaleNeighborhood (PrimeSpectrum.comap (algebraMap R S) q) :=
  of q rfl hres

/-- The carrier of an explicitly bundled etale neighborhood is the supplied
etale algebra. -/
@[simp]
theorem carrier_of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal)
    (hres : Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hq)) :
    (of q hq hres).carrier = S := sorry

/-- The selected point of an explicitly bundled etale neighborhood is the
supplied point. -/
@[simp]
theorem point_of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal)
    (hres : Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hq)) :
    (of q hq hres).point = q := sorry

/-- The selected point of an etale neighborhood of a maximal point is
maximal. -/
@[stacks 07QZ "maximal point of an etale neighborhood"]
theorem point_isMaximal {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    [p.asIdeal.IsMaximal] (U : EtaleNeighborhood p) :
    U.point.asIdeal.IsMaximal := sorry

/-- The bundled point of an etale neighborhood maps to its base point. -/
theorem comap_point {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood p) :
    PrimeSpectrum.comap (algebraMap R U.carrier) U.point = p := sorry

/-- The structural map of an etale neighborhood is residue-field bijective
at its selected point. -/
@[stacks 07QZ "pointwise residue-field property of an etale neighborhood"]
theorem residueFieldBijectiveAt {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p) :
    RingHom.ResidueField.IsBijectiveAt
      (algebraMap R U.carrier) U.point := sorry

/-- The etale, lying-over, and residue-field conditions carried
by an etale neighborhood. -/
@[stacks 07QZ "etale neighborhood specification"]
theorem spec {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood p) :
    Algebra.Etale R U.carrier ∧
      PrimeSpectrum.comap (algebraMap R U.carrier) U.point = p ∧
      RingHom.ResidueField.IsBijectiveAt
        (algebraMap R U.carrier) U.point := sorry

/-- The residue-field map of an etale neighborhood, in algebra-hom form, is bijective. -/
@[stacks 07QZ "residue field map of an etale neighborhood"]
theorem residueFieldMapₐ_bijective {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ p.asIdeal U.point.asIdeal (Algebra.ofId R U.carrier) U.over) := sorry

/-- The canonical residue-field algebra equivalence of an etale neighborhood. -/
@[stacks 07QZ "residue field algebra equivalence of an etale neighborhood"]
noncomputable def residueFieldAlgEquiv {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p) :
    p.asIdeal.ResidueField ≃ₐ[R] U.point.asIdeal.ResidueField :=
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ p.asIdeal U.point.asIdeal (Algebra.ofId R U.carrier) U.over)
    U.residueField_bijective

/-- The canonical residue-field ring equivalence underlying the algebra
equivalence of an etale neighborhood. -/
@[stacks 07QZ "residue field equivalence of an etale neighborhood"]
noncomputable def residueFieldEquiv {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p) :
    p.asIdeal.ResidueField ≃+* U.point.asIdeal.ResidueField :=
  U.residueFieldAlgEquiv.toRingEquiv

/-- Forgetting scalar compatibility from the canonical algebra equivalence
recovers the canonical ring equivalence. -/
@[simp]
theorem residueFieldAlgEquiv_toRingEquiv {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p) :
    U.residueFieldAlgEquiv.toRingEquiv = U.residueFieldEquiv := sorry

/-- The residue-field equivalence of an etale neighborhood is induced by the
structural algebra map. -/
@[simp]
theorem residueFieldEquiv_apply {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood p)
    (x : p.asIdeal.ResidueField) :
    U.residueFieldEquiv x =
      Ideal.ResidueField.map p.asIdeal U.point.asIdeal
        (algebraMap R U.carrier) U.over x := sorry

end EtaleNeighborhood

end PrimeSpectrum
