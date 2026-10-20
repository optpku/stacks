/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

universe u v w x

namespace RingHom

/-- An elementary étale localization of `f : R →+* S` at compatible primes `p` and `q`
stores a commutative square with étale horizontal maps, compatible primes on the new
rings, and bijective canonical maps on the two residue fields. -/
structure ElementaryEtaleLocalization {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : p.asIdeal = q.asIdeal.comap f) where
  /-- The lower-right ring `R'` in the localization square. -/
  R' : CommRingCat.{w}
  /-- The upper-right ring `S'` in the localization square. -/
  S' : CommRingCat.{x}
  /-- The étale horizontal map `R →+* R'`. -/
  base : R →+* R'
  /-- The étale horizontal map `S →+* S'`. -/
  total : S →+* S'
  /-- The right vertical map `R' →+* S'`. -/
  right : R' →+* S'
  /-- The square of ring homomorphisms commutes. -/
  commutes : right.comp base = total.comp f
  /-- The prime `p'` of `R'`. -/
  p' : PrimeSpectrum R'
  /-- The prime `q'` of `S'`. -/
  q' : PrimeSpectrum S'
  /-- The prime `p'` lies over `p`. -/
  base_comap : p.asIdeal = p'.asIdeal.comap base
  /-- The prime `q'` lies over `q`. -/
  total_comap : q.asIdeal = q'.asIdeal.comap total
  /-- The prime `q'` lies over `p'` along the right vertical map. -/
  right_comap : p'.asIdeal = q'.asIdeal.comap right
  /-- The map `R →+* R'` is étale. -/
  base_etale : base.Etale
  /-- The map `S →+* S'` is étale. -/
  total_etale : total.Etale
  /-- The canonical map `κ(p) →+* κ(p')` is bijective. -/
  base_residueField_bijective :
    Function.Bijective (Ideal.ResidueField.map p.asIdeal p'.asIdeal base base_comap)
  /-- The canonical map `κ(q) →+* κ(q')` is bijective. -/
  total_residueField_bijective :
    Function.Bijective (Ideal.ResidueField.map q.asIdeal q'.asIdeal total total_comap)

namespace ElementaryEtaleLocalization

/-- Construct an elementary étale localization from its rings, maps, primes, and defining
properties. -/
def of {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    {hq : p.asIdeal = q.asIdeal.comap f}
    (R' : CommRingCat.{w}) (S' : CommRingCat.{x})
    (base : R →+* R') (total : S →+* S') (right : R' →+* S')
    (commutes : right.comp base = total.comp f)
    (p' : PrimeSpectrum R') (q' : PrimeSpectrum S')
    (base_comap : p.asIdeal = p'.asIdeal.comap base)
    (total_comap : q.asIdeal = q'.asIdeal.comap total)
    (right_comap : p'.asIdeal = q'.asIdeal.comap right)
    (base_etale : base.Etale) (total_etale : total.Etale)
    (base_residueField_bijective :
      Function.Bijective (Ideal.ResidueField.map p.asIdeal p'.asIdeal base base_comap))
    (total_residueField_bijective :
      Function.Bijective (Ideal.ResidueField.map q.asIdeal q'.asIdeal total total_comap)) :
    ElementaryEtaleLocalization f p q hq where
  R' := R'
  S' := S'
  base := base
  total := total
  right := right
  commutes := commutes
  p' := p'
  q' := q'
  base_comap := base_comap
  total_comap := total_comap
  right_comap := right_comap
  base_etale := base_etale
  total_etale := total_etale
  base_residueField_bijective := base_residueField_bijective
  total_residueField_bijective := total_residueField_bijective

/-- Both horizontal maps of an elementary étale localization are étale. -/
theorem etale_spec {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    {hq : p.asIdeal = q.asIdeal.comap f} (L : ElementaryEtaleLocalization f p q hq) :
    L.base.Etale ∧ L.total.Etale := sorry

/-- Both canonical residue-field maps of an elementary étale localization are bijective. -/
theorem residueField_spec {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    {hq : p.asIdeal = q.asIdeal.comap f} (L : ElementaryEtaleLocalization f p q hq) :
    Function.Bijective
        (Ideal.ResidueField.map p.asIdeal L.p'.asIdeal L.base L.base_comap) ∧
      Function.Bijective
        (Ideal.ResidueField.map q.asIdeal L.q'.asIdeal L.total L.total_comap) := sorry

/-- The ring-map square, prime contractions, étaleness conditions, and canonical
residue-field maps satisfy all defining properties of an elementary étale localization. -/
theorem spec {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    {hq : p.asIdeal = q.asIdeal.comap f} (L : ElementaryEtaleLocalization f p q hq) :
    L.right.comp L.base = L.total.comp f ∧
      p.asIdeal = L.p'.asIdeal.comap L.base ∧
      q.asIdeal = L.q'.asIdeal.comap L.total ∧
      L.p'.asIdeal = L.q'.asIdeal.comap L.right ∧
      L.base.Etale ∧ L.total.Etale ∧
      Function.Bijective
          (Ideal.ResidueField.map p.asIdeal L.p'.asIdeal L.base L.base_comap) ∧
        Function.Bijective
          (Ideal.ResidueField.map q.asIdeal L.q'.asIdeal L.total L.total_comap) := sorry

end ElementaryEtaleLocalization

end RingHom
